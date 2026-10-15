//! SMT-LIB2 字面量编码（`06 §6.2.3`，修正 `B-28`）。
//!
//! 关键点：
//! - `Int` 负数**无负字面量**，须用一元 `(- n)`；
//! - `Real` 分母为 1 时用 Decimal（`5.0`），否则用**精确** `(/ 5 3)`，禁止近似（`03 §3.2.3 N-1`）；
//! - 位向量**统一**用十进制 `(_ bvN W)`，不发射 `#x…`（规避跨求解器十六进制宽度截断差异）；
//! - 字串仅把 `"` 写成 `""`，不使用反斜杠转义（SMT-LIB 2.6 规定）。

use policylang_ast::formula::{smt_string_literal, Rational};

/// `Int` 字面量。
pub fn int_lit(v: i128) -> String {
    if v < 0 {
        format!("(- {})", v.unsigned_abs())
    } else {
        v.to_string()
    }
}

/// `Real` 字面量（精确）。
pub fn real_lit(r: &Rational) -> String {
    if r.den == 1 {
        // SMT-LIB Decimal 字面量要求小数点
        format!("{}.0", int_lit(r.num))
    } else {
        format!("(/ {} {})", int_lit(r.num), int_lit(r.den))
    }
}

/// 位向量字面量 `(_ bvN W)`。
pub fn bv_lit(v: u128, width: u32) -> String {
    format!("(_ bv{} {})", v, width)
}

pub fn bool_lit(b: bool) -> String {
    if b {
        "true".to_string()
    } else {
        "false".to_string()
    }
}

/// 字串字面量。
pub fn str_lit(s: &str) -> String {
    smt_string_literal(s)
}

/// `(to_real n)` 显式提升（`N-4`）。
pub fn to_real(inner: &str) -> String {
    format!("(to_real {inner})")
}

/// `(_ BitVec W)` 排序名。
pub fn bv_sort(width: u32) -> String {
    format!("(_ BitVec {width})")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int_negative_uses_unary_minus() {
        assert_eq!(int_lit(5), "5");
        assert_eq!(int_lit(-5), "(- 5)");
        assert_eq!(int_lit(0), "0");
        assert_eq!(int_lit(i128::MIN), "(- 170141183460469231731687303715884105728)");
    }

    #[test]
    fn real_is_exact() {
        assert_eq!(real_lit(&Rational::from_int(5)), "5.0");
        assert_eq!(real_lit(&Rational::new(5, 3).unwrap()), "(/ 5 3)");
        assert_eq!(real_lit(&Rational::new(-1, 2).unwrap()), "(/ (- 1) 2)");
    }

    #[test]
    fn bv_uses_decimal_form() {
        assert_eq!(bv_lit(0x0A00_0100, 32), "(_ bv167772416 32)");
        assert_eq!(bv_sort(32), "(_ BitVec 32)");
    }

    #[test]
    fn string_escapes_only_quote() {
        assert_eq!(str_lit("a\"b\\c"), "\"a\"\"b\\c\"");
    }
}
