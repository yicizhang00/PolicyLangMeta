//! 交叉验证：**SAT 模型重放**（`FR-9`、`06 §6.7.1`、`DD-5`）。
//!
//! 目标：杜绝求解器底层 Bug 导致的**误报**。做法是把求解器给出的模型代入**规范自身的
//! 求值器**（而非求解器），独立复核断言是否真的成立。
//!
//! ## 求值器的确定性要求
//! - 精确算术：`Int` 用 `i128`、`Real` 用 [`Rational`]，**禁用浮点**（`03 §3.2.3 N-1`）；
//! - 正则：以 `R_sub` → `RegLan` 的**同一转译器**为输入（`guardian::parse_r_sub`），
//!   故复核与编码共享一份语义来源。

use std::collections::BTreeMap;

use policylang_ast::formula::{
    ArithOp, Atom, BvOp, CmpOp, Expr, ExprKind, Formula, FormulaKind, Rational, RegLan,
};
use policylang_check::guardian::parse_r_sub;
use policylang_check::typecheck::GroundSortCtx;
use policylang_diagnostics::model::{as_int, Assignment, Value};

/// 重放结论。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Replay {
    /// 模型确实满足公式（独立复核通过）。
    Holds,
    /// 模型**不**满足公式 ⇒ 求解器结果不可信。
    Fails(String),
    /// 无法复核（缺值或含未支持构造）——**保守**，不作任何结论。
    Unavailable(String),
}

impl Replay {
    pub fn is_holds(&self) -> bool {
        matches!(self, Replay::Holds)
    }
}

/// 代入模型重放公式。
pub fn replay(f: &Formula, a: &Assignment, sorts: &GroundSortCtx<'_>) -> Replay {
    match eval_formula(f, a, sorts) {
        Ok(true) => Replay::Holds,
        Ok(false) => Replay::Fails("模型不满足被断言的公式".into()),
        Err(why) => Replay::Unavailable(why),
    }
}

/// 求值公式。`Err` 表示无法复核（缺值/未支持）。
pub fn eval_formula(
    f: &Formula,
    a: &Assignment,
    sorts: &GroundSortCtx<'_>,
) -> Result<bool, String> {
    match &f.kind {
        FormulaKind::True => Ok(true),
        FormulaKind::False => Ok(false),
        FormulaKind::Atom(at) => eval_atom(at, a, sorts),
        FormulaKind::Not(x) => Ok(!eval_formula(x, a, sorts)?),
        FormulaKind::And(v) => {
            for x in v {
                if !eval_formula(x, a, sorts)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        FormulaKind::Or(v) => {
            for x in v {
                if eval_formula(x, a, sorts)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        FormulaKind::Implies(p, q) => {
            let pv = eval_formula(p, a, sorts)?;
            if !pv {
                Ok(true)
            } else {
                eval_formula(q, a, sorts)
            }
        }
        FormulaKind::Iff(p, q) => {
            let pv = eval_formula(p, a, sorts)?;
            let qv = eval_formula(q, a, sorts)?;
            Ok(pv == qv)
        }
        FormulaKind::MatchesAll { subject, patterns } => {
            let s = match eval_expr(subject, a, sorts)? {
                Value::Str(s) => s,
                other => return Err(format!("matches_all 的被匹配项不是字串：{other:?}")),
            };
            for p in patterns {
                let re = match parse_r_sub(p, f.span) {
                    Ok(r) => r,
                    Err(_) => return Err(format!("正则 `{p}` 无法转译，跳过复核")),
                };
                if !reglan_full_match(&re, &s) {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        FormulaKind::InCidr { subject, cidr } => {
            let (v, w) = match eval_expr(subject, a, sorts)? {
                Value::Bv(v, w) => (v, w),
                other => return Err(format!("in_cidr 的被检查项不是位向量：{other:?}")),
            };
            if w != cidr.width {
                return Err(format!("位宽不匹配：{w} vs {}", cidr.width));
            }
            let mask = cidr.mask();
            Ok((v & mask) == (cidr.net0 & mask))
        }
        FormulaKind::InRange {
            subject,
            width,
            lo_val,
            hi_val,
            ..
        } => {
            let (v, w) = match eval_expr(subject, a, sorts)? {
                Value::Bv(v, w) => (v, w),
                other => return Err(format!("in_range 的被检查项不是位向量：{other:?}")),
            };
            if w != *width {
                return Err(format!("位宽不匹配：{w} vs {width}"));
            }
            Ok(v >= *lo_val && v <= *hi_val)
        }
        FormulaKind::Unique { .. } => Err("`unique` 应在展开后被消去".into()),
        FormulaKind::Forall { .. } | FormulaKind::Exists { .. } => {
            Err("公式仍有量词：应在展开后再重放".into())
        }
    }
}

fn eval_atom(at: &Atom, a: &Assignment, sorts: &GroundSortCtx<'_>) -> Result<bool, String> {
    match at {
        Atom::Bool(e) => match eval_expr(e, a, sorts)? {
            Value::Bool(b) => Ok(b),
            other => Err(format!("布尔原子求值结果非布尔：{other:?}")),
        },
        Atom::Cmp { lhs, op, rhs } => {
            let l = eval_expr(lhs, a, sorts)?;
            let r = eval_expr(rhs, a, sorts)?;
            cmp_values(&l, *op, &r)
        }
    }
}

fn cmp_values(l: &Value, op: CmpOp, r: &Value) -> Result<bool, String> {
    // 字面量提升：Int ↔ Real 的比较（与 codegen 的 `promote_literal` 对齐）
    let (l, r) = match (l, r) {
        (Value::Int(a), Value::Real(b)) => (Value::Real(Rational::from_int(*a)), Value::Real(*b)),
        (Value::Real(a), Value::Int(b)) => (Value::Real(*a), Value::Real(Rational::from_int(*b))),
        (a, b) => (a.clone(), b.clone()),
    };
    let ordering = |x: &Value, y: &Value| -> Result<std::cmp::Ordering, String> {
        match (x, y) {
            (Value::Int(a), Value::Int(b)) => Ok(a.cmp(b)),
            (Value::Real(a), Value::Real(b)) => Ok((a.num * b.den).cmp(&(b.num * a.den))),
            (Value::Bv(a, _), Value::Bv(b, _)) => Ok(a.cmp(b)),
            (Value::Str(a), Value::Str(b)) => Ok(a.cmp(b)),
            _ => Err(format!("不可比较的值：{x:?} vs {y:?}")),
        }
    };
    match op {
        CmpOp::Eq => Ok(l == r),
        CmpOp::Ne => Ok(l != r),
        CmpOp::Lt => Ok(ordering(&l, &r)? == std::cmp::Ordering::Less),
        CmpOp::Le => Ok(ordering(&l, &r)? != std::cmp::Ordering::Greater),
        CmpOp::Gt => Ok(ordering(&l, &r)? == std::cmp::Ordering::Greater),
        CmpOp::Ge => Ok(ordering(&l, &r)? != std::cmp::Ordering::Less),
        CmpOp::StrLt => Ok(ordering(&l, &r)? == std::cmp::Ordering::Less),
        CmpOp::StrLe => Ok(ordering(&l, &r)? != std::cmp::Ordering::Greater),
    }
}

/// 求值表达式（精确算术）。
pub fn eval_expr(e: &Expr, a: &Assignment, sorts: &GroundSortCtx<'_>) -> Result<Value, String> {
    match &e.kind {
        ExprKind::IntLit(n) => Ok(Value::Int(*n)),
        ExprKind::RealLit(r) => Ok(Value::Real(*r)),
        ExprKind::BoolLit(b) => Ok(Value::Bool(*b)),
        ExprKind::StrLit(s) => Ok(Value::Str(s.clone())),
        ExprKind::Var(_) | ExprKind::Flat { .. } => {
            let sym = symbol_of(e);
            if let Some(v) = a.get(&sym) {
                return Ok(v.clone());
            }
            // 枚举成员（`a.kyc == Institutional` 形式）
            if let ExprKind::Var(n) = &e.kind {
                if let Some(i) = sorts.enum_member_value(n) {
                    return Ok(Value::Int(i));
                }
            }
            Err(format!("模型中缺少符号 `{sym}` 的赋值"))
        }
        ExprKind::FieldAccess { .. } => Err("展开后仍有 `FieldAccess`".into()),
        ExprKind::Arith { op, lhs, rhs } => {
            let l = eval_expr(lhs, a, sorts)?;
            let r = eval_expr(rhs, a, sorts)?;
            arith(*op, &l, &r)
        }
        ExprKind::Neg(x) => match eval_expr(x, a, sorts)? {
            Value::Int(i) => Ok(Value::Int(-i)),
            Value::Real(r) => Ok(Value::Real(
                Rational::new(-r.num, r.den).unwrap_or_else(|| Rational::from_int(0)),
            )),
            other => Err(format!("一元负号作用于非数值：{other:?}")),
        },
        ExprKind::StrLen(x) => match eval_expr(x, a, sorts)? {
            Value::Str(s) => Ok(Value::Int(s.chars().count() as i128)),
            other => Err(format!("str.len 作用于非字串：{other:?}")),
        },
        ExprKind::ToReal(x) => match eval_expr(x, a, sorts)? {
            Value::Int(i) => Ok(Value::Real(Rational::from_int(i))),
            other @ Value::Real(_) => Ok(other),
            other => Err(format!("to_real 作用于非整数：{other:?}")),
        },
        ExprKind::Int2Bv { width, value } => match eval_expr(value, a, sorts)? {
            Value::Int(i) => {
                let mask = if *width >= 128 {
                    u128::MAX
                } else {
                    (1u128 << width) - 1
                };
                Ok(Value::Bv((i as u128) & mask, *width))
            }
            other => Err(format!("int2bv 作用于非整数：{other:?}")),
        },
        ExprKind::Bv2Int(x) => match eval_expr(x, a, sorts)? {
            Value::Bv(v, _) => Ok(Value::Int(v as i128)),
            other => Err(format!("bv2int 作用于非位向量：{other:?}")),
        },
        ExprKind::Bv { op, lhs, rhs, width } => {
            let l = match eval_expr(lhs, a, sorts)? {
                Value::Bv(v, _) => v,
                other => return Err(format!("位向量运算左操作数非位向量：{other:?}")),
            };
            if op.is_unary() {
                return Ok(Value::Bv(mask_bv(!l, *width), *width));
            }
            let r = match eval_expr(rhs, a, sorts)? {
                Value::Bv(v, _) => v,
                other => return Err(format!("位向量运算右操作数非位向量：{other:?}")),
            };
            let out = match op {
                BvOp::And => l & r,
                BvOp::Or => l | r,
                BvOp::Xor => l ^ r,
                BvOp::Not => !l,
                BvOp::Add => l.wrapping_add(r),
                BvOp::Sub => l.wrapping_sub(r),
                BvOp::Mul => l.wrapping_mul(r),
                BvOp::Shl => l << (r % (*width).max(1) as u128),
                BvOp::Lshr => l >> (r % (*width).max(1) as u128),
            };
            Ok(Value::Bv(mask_bv(out, *width), *width))
        }
    }
}

fn mask_bv(v: u128, width: u32) -> u128 {
    if width >= 128 {
        v
    } else {
        v & ((1u128 << width) - 1)
    }
}

/// 符号名（与 `naming` 的单一实现一致）。
pub fn symbol_of(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Var(n) => policylang_ast::naming::global_symbol(n),
        ExprKind::Flat {
            domain,
            index,
            field,
        } => policylang_ast::naming::scalar_symbol(domain, *index, field),
        _ => String::new(),
    }
}

fn arith(op: ArithOp, l: &Value, r: &Value) -> Result<Value, String> {
    // Int 与 Real 的提升（与 `promote_literal` 语义一致）
    let (l, r) = match (l, r) {
        (Value::Int(a), Value::Real(b)) => (Value::Real(Rational::from_int(*a)), Value::Real(*b)),
        (Value::Real(a), Value::Int(b)) => (Value::Real(*a), Value::Real(Rational::from_int(*b))),
        (a, b) => (a.clone(), b.clone()),
    };
    let as_rat = |v: &Value| -> Result<Rational, String> {
        match v {
            Value::Int(i) => Ok(Rational::from_int(*i)),
            Value::Real(r) => Ok(*r),
            other => Err(format!("算术作用于非数值：{other:?}")),
        }
    };
    match op {
        ArithOp::Add | ArithOp::Sub | ArithOp::Mul => {
            let (a, b) = (as_rat(&l)?, as_rat(&r)?);
            let n = match op {
                ArithOp::Add => a.num * b.den + b.num * a.den,
                ArithOp::Sub => a.num * b.den - b.num * a.den,
                _ => a.num * b.num,
            };
            let d = if op == ArithOp::Mul { a.den * b.den } else { a.den * b.den };
            let v = Rational::new(n, d).ok_or("有理数分母为 0")?;
            Ok(if v.is_integer() && matches!(l, Value::Int(_)) && matches!(r, Value::Int(_)) {
                Value::Int(v.num)
            } else {
                Value::Real(v)
            })
        }
        ArithOp::RealDiv => {
            let (a, b) = (as_rat(&l)?, as_rat(&r)?);
            if b.is_zero() {
                // 除零：取值未指定 ⇒ 不可复核（诚实返回 Unavailable 路径）
                return Err("除数求值为 0，取值未指定（A-12）".into());
            }
            let v = Rational::new(a.num * b.den, a.den * b.num).ok_or("有理数构造失败")?;
            Ok(if v.is_integer() && matches!(l, Value::Int(_)) && matches!(r, Value::Int(_)) {
                Value::Int(v.num)
            } else {
                Value::Real(v)
            })
        }
        ArithOp::IntDiv | ArithOp::IntMod => {
            let a = as_int(&l).ok_or("div/mod 需要整数")?;
            let b = as_int(&r).ok_or("div/mod 需要整数")?;
            if b == 0 {
                return Err("div/mod 除数为 0，取值未指定（A-12）".into());
            }
            Ok(Value::Int(if op == ArithOp::IntDiv {
                a.div_euclid(b)
            } else {
                a.rem_euclid(b)
            }))
        }
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// RegLan 整串匹配（与 SMT-LIB `str.in_re` 的「整串属于」语义一致）
// ═════════════════════════════════════════════════════════════════════════════

/// 整串匹配：`s ∈ L(re)`。
pub fn reglan_full_match(re: &RegLan, s: &str) -> bool {
    let cs: Vec<char> = s.chars().collect();
    let ends = match_ends(re, &cs, 0);
    ends.contains(&cs.len())
}

/// 返回从位置 `i` 起所有可能的**匹配结束位置**集合（位置语义的 NFA 展开）。
fn match_ends(re: &RegLan, s: &[char], i: usize) -> Vec<usize> {
    use std::collections::BTreeSet;
    let mut set: BTreeSet<usize> = BTreeSet::new();
    match re {
        RegLan::Empty => {}
        RegLan::All => {
            for k in i..=s.len() {
                set.insert(k);
            }
        }
        RegLan::AllChar => {
            if i < s.len() {
                set.insert(i + 1);
            }
        }
        RegLan::Str(t) => {
            let tc: Vec<char> = t.chars().collect();
            if s.len() >= i + tc.len() && &s[i..i + tc.len()] == &tc[..] {
                set.insert(i + tc.len());
            }
        }
        RegLan::Range(a, b) => {
            if let Some(c) = s.get(i) {
                if *a <= *c && *c <= *b {
                    set.insert(i + 1);
                }
            }
        }
        RegLan::Union(v) => {
            for x in v {
                for e in match_ends(x, s, i) {
                    set.insert(e);
                }
            }
        }
        RegLan::Inter(v) => {
            // 交集 = 各分量**结束位置集合**的交（各分量看到的是同一段 `s[i..e]`）
            let mut acc: Option<BTreeSet<usize>> = None;
            for x in v {
                let cur: BTreeSet<usize> = match_ends(x, s, i).into_iter().collect();
                acc = Some(match acc {
                    None => cur,
                    Some(prev) => prev.intersection(&cur).copied().collect(),
                });
            }
            if let Some(a) = acc {
                set.extend(a);
            } else {
                // 空交集（∩∅ = Σ*）⇒ 任意结束位置
                for k in i..=s.len() {
                    set.insert(k);
                }
            }
        }
        RegLan::Concat(v) => {
            let mut cur: BTreeSet<usize> = BTreeSet::new();
            cur.insert(i);
            for x in v {
                let mut next: BTreeSet<usize> = BTreeSet::new();
                for p in &cur {
                    for e in match_ends(x, s, *p) {
                        next.insert(e);
                    }
                }
                cur = next;
                if cur.is_empty() {
                    break;
                }
            }
            set.extend(cur);
        }
        RegLan::Opt(x) => {
            set.insert(i);
            for e in match_ends(x, s, i) {
                set.insert(e);
            }
        }
        RegLan::Star(x) | RegLan::Plus(x) => {
            // 闭包：不动点迭代（串长有限 ⇒ 终止）
            let one: RegLan = (**x).clone();
            let mut reach: BTreeSet<usize> = BTreeSet::new();
            if matches!(re, RegLan::Star(_)) {
                reach.insert(i);
            }
            let mut frontier: Vec<usize> = vec![i];
            while let Some(p) = frontier.pop() {
                for e in match_ends(&one, s, p) {
                    if e == p {
                        continue; // 零宽匹配，避免死循环
                    }
                    if reach.insert(e) {
                        frontier.push(e);
                    }
                }
            }
            set.extend(reach);
        }
        RegLan::Loop(x, m, n) => {
            let mut cur: BTreeSet<usize> = BTreeSet::new();
            cur.insert(i);
            let max = n.unwrap_or(64).min(64);
            for step in 0..=max {
                if step >= *m {
                    set.extend(cur.iter().copied());
                }
                if step == max {
                    break;
                }
                let mut next: BTreeSet<usize> = BTreeSet::new();
                for p in &cur {
                    for e in match_ends(x, s, *p) {
                        next.insert(e);
                    }
                }
                if next.is_empty() {
                    break;
                }
                cur = next;
            }
        }
        RegLan::Complement(x) => {
            // 补集：所有**不属于** `L(x)` 的子串 `s[i..e]` 都是合法结束位置（含 `ε`）
            let inner: BTreeSet<usize> = match_ends(x, s, i).into_iter().collect();
            for e in i..=s.len() {
                if !inner.contains(&e) {
                    set.insert(e);
                }
            }
        }
    }
    set.into_iter().collect()
}

/// 便利：批量重放并汇总（`06 §6.7.1` 的判定表）。
pub fn crossval_summary(replays: &[Replay]) -> (usize, usize, usize) {
    let holds = replays.iter().filter(|r| matches!(r, Replay::Holds)).count();
    let fails = replays.iter().filter(|r| matches!(r, Replay::Fails(_))).count();
    let unavail = replays.len() - holds - fails;
    (holds, fails, unavail)
}

/// 空赋值（测试用）。
pub fn empty_assignment() -> Assignment {
    BTreeMap::new()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reglan_matches_full_string_semantics() {
        let any = RegLan::Star(Box::new(RegLan::AllChar));
        // `.*[A-Z].*`
        let has_upper = RegLan::Concat(vec![any.clone(), RegLan::Range('A', 'Z'), any.clone()]);
        assert!(reglan_full_match(&has_upper, "abcD"));
        assert!(reglan_full_match(&has_upper, "D"));
        assert!(!reglan_full_match(&has_upper, "abcd"));
        // `[A-Z].*`
        let starts_upper = RegLan::Concat(vec![RegLan::Range('A', 'Z'), any.clone()]);
        assert!(reglan_full_match(&starts_upper, "Ab1"));
        assert!(!reglan_full_match(&starts_upper, "aB1"));
        // 交替与量词
        let alt = RegLan::Union(vec![RegLan::Str("ab".into()), RegLan::Str("cd".into())]);
        assert!(reglan_full_match(&alt, "ab"));
        assert!(!reglan_full_match(&alt, "abc"));
        let looped = RegLan::Loop(Box::new(RegLan::Str("ab".into())), 2, Some(3));
        assert!(reglan_full_match(&looped, "abab"));
        assert!(reglan_full_match(&looped, "ababab"));
        assert!(!reglan_full_match(&looped, "ab"));
        // 补集
        let not_digit = RegLan::Complement(Box::new(RegLan::Range('0', '9')));
        assert!(reglan_full_match(&not_digit, "x"));
        assert!(!reglan_full_match(&not_digit, "5"));
    }

    #[test]
    fn parse_and_match_roundtrip() {
        let re = parse_r_sub(".*[A-Z].*", policylang_ast::Span::default()).unwrap();
        assert!(reglan_full_match(&re, "aBc"));
    }
}
