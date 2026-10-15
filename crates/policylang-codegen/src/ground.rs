//! 有界量词展开 `ALG-1`（`03 §3.6`、`§3.7 TH-1`、`§3.8 TH-2`）。
//!
//! 产出**无量词**公式（`INV-G`），所有域实例以 [`ExprKind::Flat`] 表示。
//!
//! ## 实现要求（`03 §3.6` 的 8 条）
//! | 编号 | 要求 | 本实现 |
//! |---|---|---|
//! | `INV-G` | 输出不含 `Forall`/`Exists` | 递归消除，唯一构造点为 `And`/`Or` 折叠 |
//! | `DET-1` | 枚举顺序确定（首位外层、末位内层） | [`enumerate_tuples`] 结构化递增 |
//! | `DET-2` | 展平符号命名确定 | 复用 `ast::naming::scalar_symbol`（单一实现，`INV-L2`） |
//! | `FOLD-1` | 常量折叠（算术） | [`fold_expr`] |
//! | `FOLD-2` | 常量折叠（逻辑 `⊤`/`⊥` 消去） | [`Formula::and`]/[`Formula::or`] 前先化简 |
//! | `CSE-1` | 公共子式提取（此处实现**合取/析取去重**，α-等价以规范键判定） | [`dedup`] |
//! | `ALG-1-P` | 死变量剪枝 | 未被体引用的量化变量不参与枚举 |
//! | 溢出 | 枚举数超过预算即 `E-GROUNDING-BUDGET` | [`Grounder::hard_cap`] |

use std::collections::BTreeSet;

use policylang_ast::codes::E_GROUNDING_BUDGET;
use policylang_ast::diag::Diagnostic;
use policylang_ast::formula::{
    ArithOp, Atom, CmpOp, Expr, ExprKind, Formula, FormulaKind, Rational,
};
use policylang_ast::Span;

use crate::SymbolLookup;

/// 展开环境：量化变量名 → (域名, 实例索引)。
#[derive(Debug, Clone, Default)]
pub struct GroundEnv {
    binds: Vec<(String, String, usize)>,
}

impl GroundEnv {
    pub fn lookup(&self, var: &str) -> Option<(&str, usize)> {
        self.binds
            .iter()
            .rev()
            .find(|(v, _, _)| v == var)
            .map(|(_, d, i)| (d.as_str(), *i))
    }

    fn push(&mut self, var: &str, domain: &str, index: usize) {
        self.binds.push((var.to_string(), domain.to_string(), index));
    }

    fn truncate(&mut self, n: usize) {
        self.binds.truncate(n);
    }
}

/// 展开器。
pub struct Grounder<'a> {
    lookup: &'a dyn SymbolLookup,
    /// 硬上限：枚举元组数超过它即报 `E-GROUNDING-BUDGET`（防止内存爆炸）。
    pub hard_cap: usize,
    /// 已枚举的元组总数（用于诊断）。
    pub tuples_enumerated: u64,
}

impl<'a> Grounder<'a> {
    pub fn new(lookup: &'a dyn SymbolLookup, hard_cap: usize) -> Self {
        Grounder {
            lookup,
            hard_cap,
            tuples_enumerated: 0,
        }
    }

    /// 展开一个公式（`ALG-1` 主入口）。
    pub fn ground(&mut self, f: &Formula) -> Result<Formula, Diagnostic> {
        let mut env = GroundEnv::default();
        self.ground_with(f, &mut env)
    }

    fn ground_with(&mut self, f: &Formula, env: &mut GroundEnv) -> Result<Formula, Diagnostic> {
        let span = f.span;
        match &f.kind {
            FormulaKind::True => Ok(Formula::tru(span)),
            FormulaKind::False => Ok(Formula::fals(span)),
            FormulaKind::Atom(a) => Ok(Formula::new(
                FormulaKind::Atom(self.ground_atom(a, env)?),
                span,
            )),
            FormulaKind::Not(x) => Ok(Formula::new(
                FormulaKind::Not(Box::new(self.ground_with(x, env)?)),
                span,
            )),
            FormulaKind::And(v) => {
                let mut items = Vec::with_capacity(v.len());
                for x in v {
                    items.push(self.ground_with(x, env)?);
                }
                Ok(mk_and(items, span))
            }
            FormulaKind::Or(v) => {
                let mut items = Vec::with_capacity(v.len());
                for x in v {
                    items.push(self.ground_with(x, env)?);
                }
                Ok(mk_or(items, span))
            }
            FormulaKind::Implies(a, b) => Ok(Formula::new(
                FormulaKind::Implies(
                    Box::new(self.ground_with(a, env)?),
                    Box::new(self.ground_with(b, env)?),
                ),
                span,
            )),
            FormulaKind::Iff(a, b) => Ok(Formula::new(
                FormulaKind::Iff(
                    Box::new(self.ground_with(a, env)?),
                    Box::new(self.ground_with(b, env)?),
                ),
                span,
            )),
            FormulaKind::Forall {
                vars,
                domain,
                distinct,
                body,
            } => self.ground_quantifier(vars, domain, *distinct, body, env, span, true),
            FormulaKind::Exists {
                vars,
                domain,
                distinct,
                body,
            } => self.ground_quantifier(vars, domain, *distinct, body, env, span, false),
            FormulaKind::MatchesAll { subject, patterns } => {
                let subject = self.ground_expr(subject, env)?;
                Ok(Formula::new(
                    FormulaKind::MatchesAll {
                        subject,
                        patterns: patterns.clone(),
                    },
                    span,
                ))
            }
            FormulaKind::InCidr { subject, cidr } => {
                let subject = self.ground_expr(subject, env)?;
                Ok(Formula::new(
                    FormulaKind::InCidr {
                        subject,
                        cidr: cidr.clone(),
                    },
                    span,
                ))
            }
            FormulaKind::InRange {
                subject,
                lo,
                hi,
                width,
                lo_val,
                hi_val,
            } => {
                let subject = self.ground_expr(subject, env)?;
                Ok(Formula::new(
                    FormulaKind::InRange {
                        subject,
                        lo: lo.clone(),
                        hi: hi.clone(),
                        width: *width,
                        lo_val: *lo_val,
                        hi_val: *hi_val,
                    },
                    span,
                ))
            }
            FormulaKind::Unique { domain, field } => {
                // `unique(D, f)` ⟺ `⋀_{i<j} f_i ≠ f_j`
                let n = self.lookup.domain_size(domain).unwrap_or(0);
                let mut items = Vec::new();
                for i in 0..n {
                    for j in (i + 1)..n {
                        let lhs = Expr::new(
                            ExprKind::Flat {
                                domain: domain.clone(),
                                index: i as usize,
                                field: field.clone(),
                            },
                            span,
                        );
                        let rhs = Expr::new(
                            ExprKind::Flat {
                                domain: domain.clone(),
                                index: j as usize,
                                field: field.clone(),
                            },
                            span,
                        );
                        items.push(Formula::new(
                            FormulaKind::Atom(Atom::Cmp {
                                lhs,
                                op: CmpOp::Ne,
                                rhs,
                            }),
                            span,
                        ));
                    }
                }
                Ok(mk_and(items, span))
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn ground_quantifier(
        &mut self,
        vars: &[String],
        domain: &str,
        distinct: bool,
        body: &Formula,
        env: &mut GroundEnv,
        span: Span,
        is_forall: bool,
    ) -> Result<Formula, Diagnostic> {
        let n = self.lookup.domain_size(domain).unwrap_or(0);

        // 空域：`∀ → ⊤`，`∃ → ⊥`（03 §3.5.3 退化语义）
        if n == 0 {
            return Ok(if is_forall {
                Formula::tru(span)
            } else {
                Formula::fals(span)
            });
        }
        // `distinct` 且 `k > N`：不存在 `Nodup` 元组 ⇒ 同上
        if distinct && vars.len() as u64 > n {
            return Ok(if is_forall {
                Formula::tru(span)
            } else {
                Formula::fals(span)
            });
        }

        // `ALG-1-P` 死变量剪枝：仅枚举体实际引用的变量
        let live: Vec<&String> = vars
            .iter()
            .filter(|v| body.occurs_instance(v))
            .collect();

        if live.is_empty() {
            // 体不引用任何绑定变量：量词退化（无需枚举）
            return self.ground_with(body, env);
        }

        let tuples = enumerate_tuples(n, live.len(), distinct, self.hard_cap)?;
        self.tuples_enumerated += tuples.len() as u64;

        let mut items = Vec::with_capacity(tuples.len());
        for t in &tuples {
            let mark = env.binds.len();
            for (v, idx) in live.iter().zip(t.iter()) {
                env.push(v, domain, *idx as usize);
            }
            items.push(self.ground_with(body, env)?);
            env.truncate(mark);
        }
        Ok(if is_forall {
            mk_and(items, span)
        } else {
            mk_or(items, span)
        })
    }

    fn ground_atom(&mut self, a: &Atom, env: &mut GroundEnv) -> Result<Atom, Diagnostic> {
        Ok(match a {
            Atom::Bool(e) => Atom::Bool(self.ground_expr(e, env)?),
            Atom::Cmp { lhs, op, rhs } => Atom::Cmp {
                lhs: self.ground_expr(lhs, env)?,
                op: *op,
                rhs: self.ground_expr(rhs, env)?,
            },
        })
    }

    /// 展开表达式：`FieldAccess{s, f}` → `Flat{D, i, f}`（`DET-2` 复用单一命名实现）。
    pub fn ground_expr(&mut self, e: &Expr, env: &mut GroundEnv) -> Result<Expr, Diagnostic> {
        let span = e.span;
        let kind = match &e.kind {
            ExprKind::FieldAccess { instance, field } => match env.lookup(instance) {
                Some((d, i)) => ExprKind::Flat {
                    domain: d.to_string(),
                    index: i,
                    field: field.clone(),
                },
                // 未经检查的输入（例如不变量在无量化上下文中引用绑定变量）——由检查器拦截。
                None => e.kind.clone(),
            },
            ExprKind::Arith { op, lhs, rhs } => ExprKind::Arith {
                op: *op,
                lhs: Box::new(self.ground_expr(lhs, env)?),
                rhs: Box::new(self.ground_expr(rhs, env)?),
            },
            ExprKind::Neg(a) => ExprKind::Neg(Box::new(self.ground_expr(a, env)?)),
            ExprKind::StrLen(a) => ExprKind::StrLen(Box::new(self.ground_expr(a, env)?)),
            ExprKind::ToReal(a) => ExprKind::ToReal(Box::new(self.ground_expr(a, env)?)),
            ExprKind::Bv2Int(a) => ExprKind::Bv2Int(Box::new(self.ground_expr(a, env)?)),
            ExprKind::Int2Bv { width, value } => ExprKind::Int2Bv {
                width: *width,
                value: Box::new(self.ground_expr(value, env)?),
            },
            ExprKind::Bv {
                op,
                lhs,
                rhs,
                width,
            } => ExprKind::Bv {
                op: *op,
                lhs: Box::new(self.ground_expr(lhs, env)?),
                rhs: Box::new(self.ground_expr(rhs, env)?),
                width: *width,
            },
            other => other.clone(),
        };
        // `FOLD-1`：常量折叠
        let grounded = Expr::new(kind, span);
        Ok(fold_expr(&grounded))
    }
}

/// 便利入口：用默认硬上限展开一个公式。
pub fn ground(
    f: &Formula,
    lookup: &dyn SymbolLookup,
    hard_cap: usize,
) -> Result<Formula, Diagnostic> {
    Grounder::new(lookup, hard_cap).ground(f)
}

/// `DET-1`：确定性枚举（首位外层、末位内层），`distinct = true` 时仅取 `Nodup` 元组。
pub fn enumerate_tuples(
    n: u64,
    k: usize,
    distinct: bool,
    hard_cap: usize,
) -> Result<Vec<Vec<u64>>, Diagnostic> {
    if k == 0 {
        return Ok(vec![vec![]]);
    }
    let mut out: Vec<Vec<u64>> = Vec::new();
    if n == 0 {
        return Ok(out);
    }
    if distinct && (k as u64) > n {
        return Ok(out);
    }
    let mut cur = vec![0u64; k];
    loop {
        let ok = if distinct {
            let mut seen = BTreeSet::new();
            cur.iter().all(|v| seen.insert(*v))
        } else {
            true
        };
        if ok {
            out.push(cur.clone());
            if out.len() > hard_cap {
                return Err(Diagnostic::error(
                    E_GROUNDING_BUDGET,
                    format!(
                        "展开枚举元组数超过硬上限 {hard_cap}（N = {n}, k = {k}, distinct = {distinct}）"
                    ),
                ));
            }
        }
        // 末位内层递增
        let mut i = k;
        loop {
            if i == 0 {
                return Ok(out);
            }
            i -= 1;
            cur[i] += 1;
            if cur[i] < n {
                for x in cur.iter_mut().skip(i + 1) {
                    *x = 0;
                }
                break;
            }
        }
    }
}

/// `FOLD-1`：算术常量折叠。
pub fn fold_expr(e: &Expr) -> Expr {
    let span = e.span;
    let kind = match &e.kind {
        ExprKind::Arith { op, lhs, rhs } => {
            let l = fold_expr(lhs);
            let r = fold_expr(rhs);
            if let (Some(a), Some(b)) = (l.as_num_lit(), r.as_num_lit()) {
                if let Some(v) = fold_arith(*op, a, b) {
                    return if v.is_integer() {
                        Expr::new(ExprKind::IntLit(v.num), span)
                    } else {
                        Expr::new(ExprKind::RealLit(v), span)
                    };
                }
            }
            ExprKind::Arith {
                op: *op,
                lhs: Box::new(l),
                rhs: Box::new(r),
            }
        }
        ExprKind::Neg(a) => {
            let inner = fold_expr(a);
            if let Some(v) = inner.as_num_lit() {
                let nv = Rational {
                    num: -v.num,
                    den: v.den,
                };
                return if nv.is_integer() {
                    Expr::new(ExprKind::IntLit(nv.num), span)
                } else {
                    Expr::new(ExprKind::RealLit(nv), span)
                };
            }
            ExprKind::Neg(Box::new(inner))
        }
        ExprKind::ToReal(a) => ExprKind::ToReal(Box::new(fold_expr(a))),
        ExprKind::StrLen(a) => {
            let inner = fold_expr(a);
            if let ExprKind::StrLit(s) = &inner.kind {
                return Expr::new(ExprKind::IntLit(s.chars().count() as i128), span);
            }
            ExprKind::StrLen(Box::new(inner))
        }
        ExprKind::Bv2Int(a) => ExprKind::Bv2Int(Box::new(fold_expr(a))),
        ExprKind::Int2Bv { width, value } => ExprKind::Int2Bv {
            width: *width,
            value: Box::new(fold_expr(value)),
        },
        ExprKind::Bv {
            op,
            lhs,
            rhs,
            width,
        } => ExprKind::Bv {
            op: *op,
            lhs: Box::new(fold_expr(lhs)),
            rhs: Box::new(fold_expr(rhs)),
            width: *width,
        },
        other => other.clone(),
    };
    Expr::new(kind, span)
}

fn fold_arith(op: ArithOp, a: Rational, b: Rational) -> Option<Rational> {
    let mul = |x: Rational, y: Rational| -> Option<Rational> {
        Rational::new(x.num.checked_mul(y.num)?, x.den.checked_mul(y.den)?)
    };
    match op {
        ArithOp::Add => Rational::new(
            a.num.checked_mul(b.den)?.checked_add(b.num.checked_mul(a.den)?)?,
            a.den.checked_mul(b.den)?,
        ),
        ArithOp::Sub => Rational::new(
            a.num.checked_mul(b.den)?.checked_sub(b.num.checked_mul(a.den)?)?,
            a.den.checked_mul(b.den)?,
        ),
        ArithOp::Mul => mul(a, b),
        ArithOp::RealDiv => {
            if b.is_zero() {
                None
            } else {
                Rational::new(a.num.checked_mul(b.den)?, a.den.checked_mul(b.num)?)
            }
        }
        // `div`/`mod` 由求解器语义处理（除零取值未指定），不做折叠
        ArithOp::IntDiv | ArithOp::IntMod => None,
    }
}

/// `FOLD-2` + `CSE-1`：合取折叠与去重。
pub fn mk_and(items: Vec<Formula>, span: Span) -> Formula {
    let mut out: Vec<Formula> = Vec::with_capacity(items.len());
    for x in items {
        match &x.kind {
            // 吸收律：`⊥ ∧ x = ⊥`
            FormulaKind::False => return Formula::fals(span),
            // 单位元：`⊤ ∧ x = x`
            FormulaKind::True => continue,
            _ => out.push(x),
        }
    }
    Formula::and(dedup(out), span)
}

/// `FOLD-2` + `CSE-1`：析取折叠与去重。
pub fn mk_or(items: Vec<Formula>, span: Span) -> Formula {
    let mut out: Vec<Formula> = Vec::with_capacity(items.len());
    for x in items {
        match &x.kind {
            // 吸收律：`⊤ ∨ x = ⊤`
            FormulaKind::True => return Formula::tru(span),
            FormulaKind::False => continue,
            _ => out.push(x),
        }
    }
    Formula::or(dedup(out), span)
}

/// `CSE-1`：α-等价（规范化后结构相等）去重，保持首次出现顺序（保序 ⇒ 可复算）。
fn dedup(items: Vec<Formula>) -> Vec<Formula> {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut out = Vec::with_capacity(items.len());
    for x in items {
        let key = canonical_key(&x);
        if seen.insert(key) {
            out.push(x);
        }
    }
    out
}

/// 规范键：稳定的结构序列化（不依赖哈希随机种子）。
pub fn canonical_key(f: &Formula) -> String {
    serde_json::to_string(f).unwrap_or_else(|_| format!("{:?}", f.kind))
}

/// `INV-G` 断言：公式中**不含**量词。
pub fn assert_quantifier_free(f: &Formula) -> Result<(), String> {
    if f.has_quantifier() {
        Err("INV-G 违反：展开输出仍含量词".into())
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{spec_of, LookupStub};

    fn ground_str(src: &str, rule_of: impl Fn(&policylang_ast::Spec) -> Formula) -> Formula {
        let spec = spec_of(src);
        let st = LookupStub::new(&spec);
        let f = rule_of(&spec);
        let mut g = Grounder::new(&st, 1_000_000);
        let out = g.ground(&f).unwrap();
        assert!(assert_quantifier_free(&out).is_ok());
        out
    }

    #[test]
    fn forall_expands_to_conjunction_of_n() {
        let out = ground_str(
            "entity E { a: Int }\ndomain D: Set[E] [size: 4]\n\
             policy P { rule R: forall s in D: s.a >= 1 }\n",
            |s| s.policies[0].rules[0].formula.clone(),
        );
        match &out.kind {
            FormulaKind::And(v) => assert_eq!(v.len(), 4),
            other => panic!("期望 And，实际 {other:?}"),
        }
    }

    #[test]
    fn distinct_prunes_diagonal() {
        let out = ground_str(
            "entity E { a: Int }\ndomain D: Set[E] [size: 4]\n\
             policy P { rule R: forall x, y in D distinct: x.a != y.a }\n",
            |s| s.policies[0].rules[0].formula.clone(),
        );
        match &out.kind {
            FormulaKind::And(v) => assert_eq!(v.len(), 12), // 4 * 3
            other => panic!("期望 And，实际 {other:?}"),
        }
    }

    #[test]
    fn dead_variable_is_pruned() {
        // `y` 未出现在体中 ⇒ 仅枚举 `x`（ALG-1-P）
        let out = ground_str(
            "entity E { a: Int }\ndomain D: Set[E] [size: 5]\n\
             policy P { rule R: forall x, y in D: x.a >= 1 }\n",
            |s| s.policies[0].rules[0].formula.clone(),
        );
        match &out.kind {
            FormulaKind::And(v) => assert_eq!(v.len(), 5),
            other => panic!("期望 And，实际 {other:?}"),
        }
    }

    #[test]
    fn exists_expands_to_disjunction() {
        let out = ground_str(
            "entity E { a: Int }\ndomain D: Set[E] [size: 3]\n\
             policy P { rule R: exists s in D: s.a > 0 }\n",
            |s| s.policies[0].rules[0].formula.clone(),
        );
        assert!(matches!(out.kind, FormulaKind::Or(_)));
    }

    #[test]
    fn unique_expands_to_pairwise_inequality() {
        let out = ground_str(
            "entity E { a: Int }\ndomain D: Set[E] [size: 4]\n\
             policy P { rule R: unique(D, a) }\n",
            |s| s.policies[0].rules[0].formula.clone(),
        );
        match &out.kind {
            FormulaKind::And(v) => assert_eq!(v.len(), 6), // C(4,2)
            other => panic!("期望 And，实际 {other:?}"),
        }
    }

    #[test]
    fn nested_quantifiers_multiply() {
        let out = ground_str(
            "entity E { a: Int }\ndomain D: Set[E] [size: 3]\n\
             policy P { rule R: forall x in D: exists y in D: x.a == y.a }\n",
            |s| s.policies[0].rules[0].formula.clone(),
        );
        match &out.kind {
            FormulaKind::And(v) => {
                assert_eq!(v.len(), 3);
                for x in v {
                    assert!(matches!(x.kind, FormulaKind::Or(_)));
                }
            }
            other => panic!("期望 And，实际 {other:?}"),
        }
    }

    #[test]
    fn cse_dedups_identical_conjuncts() {
        let out = ground_str(
            "entity E { a: Int }\ndomain D: Set[E] [size: 3]\n\
             policy P { rule R: forall x in D: (x.a >= 1) and (x.a >= 1) }\n",
            |s| s.policies[0].rules[0].formula.clone(),
        );
        // 展开后每个实例内的重复合取被去重 ⇒ 3 个（而非 6 个）
        match &out.kind {
            FormulaKind::And(v) => assert_eq!(v.len(), 3),
            other => panic!("期望 And，实际 {other:?}"),
        }
    }

    #[test]
    fn empty_domain_semantics() {
        // 域 size 会在检查期被拒，此处直接验证枚举函数
        assert_eq!(enumerate_tuples(0, 2, false, 10).unwrap().len(), 0);
        assert_eq!(enumerate_tuples(3, 5, true, 10).unwrap().len(), 0);
        assert_eq!(enumerate_tuples(3, 2, false, 100).unwrap().len(), 9);
        assert_eq!(enumerate_tuples(3, 2, true, 100).unwrap().len(), 6);
        // 顺序：首位外层（DET-1）
        let t = enumerate_tuples(2, 2, false, 100).unwrap();
        assert_eq!(t, vec![vec![0, 0], vec![0, 1], vec![1, 0], vec![1, 1]]);
    }

    #[test]
    fn hard_cap_is_enforced() {
        let e = enumerate_tuples(1000, 3, false, 10).unwrap_err();
        assert_eq!(e.code, E_GROUNDING_BUDGET);
    }

    #[test]
    fn constant_folding() {
        let s = Span::new(1, 1, 1, 1);
        let e = Expr::new(
            ExprKind::Arith {
                op: ArithOp::Add,
                lhs: Box::new(Expr::new(ExprKind::IntLit(2), s)),
                rhs: Box::new(Expr::new(ExprKind::IntLit(3), s)),
            },
            s,
        );
        assert_eq!(fold_expr(&e).as_int_lit(), Some(5));
        let d = Expr::new(
            ExprKind::Arith {
                op: ArithOp::RealDiv,
                lhs: Box::new(Expr::new(ExprKind::IntLit(1), s)),
                rhs: Box::new(Expr::new(ExprKind::IntLit(2), s)),
            },
            s,
        );
        assert_eq!(fold_expr(&d).as_num_lit(), Some(Rational { num: 1, den: 2 }));
    }

    #[test]
    fn logical_folding_and_cse() {
        let s = Span::new(1, 1, 1, 1);
        assert!(matches!(mk_and(vec![Formula::tru(s)], s).kind, FormulaKind::True));
        assert!(matches!(mk_and(vec![Formula::fals(s)], s).kind, FormulaKind::False));
        assert!(matches!(mk_or(vec![Formula::tru(s)], s).kind, FormulaKind::True));
        let a = Formula::new(
            FormulaKind::Atom(Atom::Bool(Expr::new(ExprKind::BoolLit(true), s))),
            s,
        );
        let out = mk_and(vec![a.clone(), a], s);
        assert!(matches!(out.kind, FormulaKind::Atom(_)));
    }
}
