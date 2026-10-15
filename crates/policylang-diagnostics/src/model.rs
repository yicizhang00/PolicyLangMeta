//! 求解器模型的解析与还原（`07 §7.2`）。
//!
//! 把 `(get-model)` 的 S-Expr 还原为「SMT 符号 → 值」的赋值表。求解器间格式差异
//! （`(model …)` 包裹、`define-fun` 平铺、`#x`/`(_ bvN W)` 混用）由本模块吸收。

use std::collections::BTreeMap;

use policylang_ast::formula::Rational;

use crate::sexpr::SExpr;

/// 一个具体的值。
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i128),
    Real(Rational),
    Bool(bool),
    Bv(u128, u32),
    Str(String),
    /// 无法识别的形式（保留原文以诚实呈现，不静默丢弃）。
    Unknown(String),
}

/// 完整赋值表（符号 → 值）。
pub type Assignment = BTreeMap<String, Value>;

/// 从一组顶层表达式提取赋值（兼容 `(model …)` 与平铺 `(define-fun …)`）。
pub fn extract_assignments(exprs: &[SExpr]) -> Assignment {
    let mut out = Assignment::new();
    for e in exprs {
        collect(e, &mut out);
    }
    out
}

fn collect(e: &SExpr, out: &mut Assignment) {
    let Some(list) = e.as_list() else { return };
    match list.first().and_then(SExpr::as_atom) {
        Some("model") => {
            for x in &list[1..] {
                collect(x, out);
            }
        }
        Some("define-fun") | Some("define-fun-rec") => {
            // (define-fun <name> () <sort> <value>)
            let name = list.get(1).and_then(SExpr::as_atom).map(str::to_string);
            let Some(name) = name else { return };
            if list.len() < 5 {
                return; // 带参数的函数定义（本框架不产生）
            }
            let sort = list.get(3);
            let val = list.get(4).unwrap();
            out.insert(name, value_of(val, sort));
        }
        _ => {
            // ── 容错：**裸定义列表**形式的模型 ────────────────────────────────────
            // 实测 z3 5.3.0 与 cvc5 1.4.2 的 `(get-model)` 输出**不含 `model` 关键字**，
            // 而是直接给出定义列表：`((define-fun x () Int 7) …)`。
            // SMT-LIB2 的标准形式是 `(model (define-fun …))`，因此**两种都必须接受**
            // （否则反例还原静默失效：模型解析为空 ⇒ 报告缺失业务可读反例）。
            //
            // 判定条件刻意**收紧**：只有当列表中**确实存在** `define-fun`/`model` 头的子列表时
            // 才按容器递归，避免对 `(A B)`（Unsat Core）或 `(error "…")` 产生误提取。
            let container = list.iter().any(|x| {
                x.as_list()
                    .and_then(|l| l.first())
                    .and_then(SExpr::as_atom)
                    .map_or(false, |h| matches!(h, "define-fun" | "define-fun-rec" | "model"))
            });
            if container {
                for x in list {
                    collect(x, out);
                }
            }
            // 其它列表（如 `(error …)`）忽略
        }
    }
}

/// 解析一个字面量值；`sort` 供 `Enum`（整数编码）消歧。
pub fn value_of(e: &SExpr, _sort: Option<&SExpr>) -> Value {
    match e {
        SExpr::Str(s) => Value::Str(s.clone()),
        SExpr::Atom(a) => parse_atom(a),
        SExpr::List(v) => {
            // `(- 5)` / `(/ 5 3)` / `(_ bv5 32)` / `(as …)` / `((- 5))`
            match v.first().and_then(SExpr::as_atom) {
                Some("-") if v.len() == 2 => match value_of(&v[1], None) {
                    Value::Int(i) => Value::Int(-i),
                    Value::Real(r) => Value::Real(
                        Rational::new(-r.num, r.den).unwrap_or(Rational::from_int(0)),
                    ),
                    other => other,
                },
                Some("/") if v.len() == 3 => {
                    let n = match value_of(&v[1], None) {
                        Value::Int(i) => i,
                        _ => 0,
                    };
                    let d = match value_of(&v[2], None) {
                        Value::Int(i) => i,
                        _ => 1,
                    };
                    Value::Real(Rational::new(n, d).unwrap_or_else(|| Rational::from_int(n)))
                }
                Some("_") if v.len() == 3 => match (v[1].as_atom(), v[2].as_atom()) {
                    (Some(bv), Some(w)) if bv.starts_with("bv") => {
                        let val = bv[2..].parse::<u128>().unwrap_or(0);
                        let width = w.parse::<u32>().unwrap_or(32);
                        Value::Bv(val, width)
                    }
                    _ => Value::Unknown(e.to_text()),
                },
                Some("as") => v
                    .get(1)
                    .map(|x| value_of(x, None))
                    .unwrap_or(Value::Unknown(e.to_text())),
                _ => Value::Unknown(e.to_text()),
            }
        }
    }
}

/// 把模型值渲染为**合法的 SMT-LIB2 字面量**（供反例区间化的固定断言，`06 §6.3.7`）。
///
/// 与 [`crate::format_value`]（面向人类阅读）相对：本函数面向**机器**，
/// 必须产出可直接嵌入 `(assert (= sym <字面量>))` 的文本。
pub fn smt_literal(v: &Value, sort: &policylang_ast::formula::Sort) -> String {
    use policylang_ast::formula::Sort;
    match (v, sort) {
        // 枚举（整数编码）：下标；枚举（datatype）：零元构造子
        (Value::Int(i), Sort::Enum(_)) => i.to_string(),
        (Value::Str(s), Sort::Enum(_)) => policylang_ast::naming::enum_ctor_name(s),
        (Value::Int(i), _) => {
            if *i < 0 {
                format!("(- {})", -(*i as i128))
            } else {
                i.to_string()
            }
        }
        (Value::Real(r), _) => {
            let mag = if r.den == 1 {
                format!("{}.0", r.num.abs())
            } else {
                format!("(/ {} {})", r.num.abs(), r.den)
            };
            if r.num < 0 {
                format!("(- {mag})")
            } else {
                mag
            }
        }
        (Value::Bool(b), _) => b.to_string(),
        // SMT-LIB 2.6：字串内的 `"` 写作 `""`
        (Value::Str(s), _) => format!("\"{}\"", s.replace('"', "\"\"")),
        (Value::Bv(x, w), _) => {
            let w = if *w == 0 { 32 } else { *w };
            format!("(_ bv{x} {w})")
        }
        // 未识别的值：原样透传（可能是求解器私有形式），交由求解器判定
        (Value::Unknown(s), _) => s.clone(),
    }
}

fn parse_atom(a: &str) -> Value {
    match a {
        "true" => return Value::Bool(true),
        "false" => return Value::Bool(false),
        _ => {}
    }
    // datatype 编码的枚举（`DD-6.2` 的保留开关）：`PL_M_<escaped member>` ⇒ 成员名。
    // 无需排序表即可还原（构造子名自带成员信息，`naming::enum_ctor_name`）。
    if let Some(rest) = a.strip_prefix("PL_M_") {
        return Value::Str(policylang_ast::naming::unescape(rest));
    }
    if let Some(hex) = a.strip_prefix("#x") {
        let val = u128::from_str_radix(hex, 16).unwrap_or(0);
        return Value::Bv(val, (hex.len() * 4) as u32);
    }
    if let Some(bin) = a.strip_prefix("#b") {
        let val = u128::from_str_radix(bin, 2).unwrap_or(0);
        return Value::Bv(val, bin.len() as u32);
    }
    if a.contains('.') {
        if let Some(r) = Rational::parse_decimal(a) {
            return Value::Real(r);
        }
    }
    if let Ok(i) = a.parse::<i128>() {
        return Value::Int(i);
    }
    Value::Unknown(a.to_string())
}

/// 取整数值（`Int` 或 `Enum` 编码）。
pub fn as_int(v: &Value) -> Option<i128> {
    match v {
        Value::Int(i) => Some(*i),
        Value::Real(r) if r.is_integer() => Some(r.num),
        Value::Bv(x, _) => Some(*x as i128),
        _ => None,
    }
}

/// 取位向量值（含位宽）。
pub fn as_bv(v: &Value) -> Option<(u128, u32)> {
    match v {
        Value::Bv(x, w) => Some((*x, *w)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexpr::parse_all;

    #[test]
    fn parses_model_forms() {
        let src = r#"(model
            (define-fun PL_g_p () Int 80)
            (define-fun PL_D_0_ip () (_ BitVec 32) (_ bv167772416 32))
            (define-fun PL_D_0_b () Bool true)
            (define-fun PL_D_0_r () Real (/ 1 2))
            (define-fun PL_D_0_s () String "abc")
        )"#;
        let a = extract_assignments(&parse_all(src).unwrap());
        assert_eq!(a["PL_g_p"], Value::Int(80));
        assert_eq!(a["PL_D_0_ip"], Value::Bv(167772416, 32));
        assert_eq!(a["PL_D_0_b"], Value::Bool(true));
        assert_eq!(a["PL_D_0_r"], Value::Real(Rational::new(1, 2).unwrap()));
        assert_eq!(a["PL_D_0_s"], Value::Str("abc".into()));
    }

    #[test]
    fn parses_negative_and_hex() {
        let a = extract_assignments(&parse_all("(define-fun x () Int (- 7))\n(define-fun y () (_ BitVec 8) #x0a)").unwrap());
        assert_eq!(a["x"], Value::Int(-7));
        assert_eq!(a["y"], Value::Bv(10, 8));
    }

    #[test]
    fn unknown_values_are_preserved() {
        let a = extract_assignments(&parse_all("(define-fun z () T (f 1))").unwrap());
        assert!(matches!(a["z"], Value::Unknown(ref s) if s.contains("f")));
    }

    #[test]
    fn flattens_flat_define_funs() {
        let a = extract_assignments(&parse_all("(define-fun a () Int 1)(define-fun b () Int 2)").unwrap());
        assert_eq!(a.len(), 2);
    }
}
