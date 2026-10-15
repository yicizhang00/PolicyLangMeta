//! 展开规模度量 `G(φ)` 与预算守卫 `W11`（`03 §3.9`）。
//!
//! ## 度量定义
//!
//! 规范给出 `G(φ) = A(φ) · ∏ N^{k'}`（单一量词前缀形式）。对**混合结构**（量词出现在
//! 合取/析取的分支中）乘积形式不成立，故本实现采用与之相容的**求和推广**：
//!
//! ```text
//! atoms(原子)                    = 1
//! atoms(True/False)              = 1
//! atoms(¬a)                      = atoms(a)
//! atoms(a ∧ b) = atoms(a ∨ b)    = atoms(a) + atoms(b)
//! atoms(a → b) = atoms(a ↔ b)    = atoms(a) + atoms(b)
//! atoms(∀x̄∈D. b) = atoms(∃x̄∈D. b) = mult(N, k, distinct) · atoms(b)
//! atoms(unique(D, f))            = C(N, 2)
//! atoms(in_cidr / in_range / matches_all) = 1
//! ```
//! 其中 `mult = N^k`（`AX-Q-INDEP` 全笛卡尔积）或 `N·(N−1)···(N−k+1)`（`distinct` 单射枚举）。
//! `G(φ) ≜ atoms(φ)` 即**全量展开后待发射的原子数**——这是编译与求解真实代价的度量。
//!
//! 全部运算使用 `u128` 中间量并在 `cap` 处饱和，避免溢出掩盖问题；溢出即视为超预算。

use policylang_ast::formula::{Expr, ExprKind, Formula, FormulaKind};
use policylang_ast::spec::Spec;

/// 预算默认上限 `G_max`（`03 §3.9`）。
pub const G_MAX_DEFAULT: u128 = 1_000_000;

/// 展开度量结果。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GroundMeasure {
    /// 展开前原子数（量词乘子取 1）——即源级复杂度 `A(φ)`。
    pub atoms_before: u128,
    /// 展开后总原子数 `G(φ)`（饱和于 `cap`）。
    pub atoms_after: u128,
    /// 是否发生饱和（即确定超预算）。
    pub overflow: bool,
}

/// 单个公式的展开度量。`size_of` 返回域名 → 实例数；未声明的域按 0 处理（由其它检查报错）。
pub fn measure_formula(
    f: &Formula,
    size_of: &dyn Fn(&str) -> u64,
    cap: u128,
) -> GroundMeasure {
    let mut overflow = false;
    let after = walk(f, size_of, cap, true, &mut overflow);
    let before = walk(f, size_of, cap, false, &mut overflow);
    GroundMeasure {
        atoms_before: before,
        atoms_after: after,
        overflow,
    }
}

fn sat_mul(a: u128, b: u128, cap: u128, overflow: &mut bool) -> u128 {
    match a.checked_mul(b) {
        Some(v) if v <= cap => v,
        _ => {
            *overflow = true;
            cap
        }
    }
}

fn sat_add(a: u128, b: u128, cap: u128, overflow: &mut bool) -> u128 {
    let v = a.saturating_add(b);
    if v > cap {
        *overflow = true;
        return cap;
    }
    v
}

/// `distinct = false` 时 `N^k`；`true` 时为下降阶乘 `N·(N−1)···(N−k+1)`（`Inj` 枚举）。
fn tuple_mult(n: u64, k: usize, distinct: bool, cap: u128, overflow: &mut bool) -> u128 {
    let mut acc: u128 = 1;
    if distinct {
        for i in 0..k {
            let factor = (n as u128).saturating_sub(i as u128);
            // `k > N` ⇒ 无满足 `Nodup` 的元组 ⇒ 全称量词恒真、存在量词恒假；
            // 对应展开乘积为 0。
            acc = sat_mul(acc, factor, cap, overflow);
        }
    } else {
        for _ in 0..k {
            acc = sat_mul(acc, n as u128, cap, overflow);
        }
    }
    acc
}

fn walk(
    f: &Formula,
    size_of: &dyn Fn(&str) -> u64,
    cap: u128,
    apply_quant: bool,
    overflow: &mut bool,
) -> u128 {
    match &f.kind {
        FormulaKind::True | FormulaKind::False => 1,
        FormulaKind::Atom(_) | FormulaKind::MatchesAll { .. } => 1,
        FormulaKind::InCidr { .. } | FormulaKind::InRange { .. } => 1,
        FormulaKind::Not(a) => walk(a, size_of, cap, apply_quant, overflow),
        FormulaKind::And(v) | FormulaKind::Or(v) => {
            let mut s = 0u128;
            for x in v {
                s = sat_add(s, walk(x, size_of, cap, apply_quant, overflow), cap, overflow);
            }
            s
        }
        FormulaKind::Implies(a, b) | FormulaKind::Iff(a, b) => {
            let s = walk(a, size_of, cap, apply_quant, overflow);
            let t = walk(b, size_of, cap, apply_quant, overflow);
            sat_add(s, t, cap, overflow)
        }
        FormulaKind::Forall {
            vars,
            domain,
            distinct,
            body,
        }
        | FormulaKind::Exists {
            vars,
            domain,
            distinct,
            body,
        } => {
            let inner = walk(body, size_of, cap, apply_quant, overflow);
            if !apply_quant {
                return inner;
            }
            let n = size_of(domain);
            let m = tuple_mult(n, vars.len(), *distinct, cap, overflow);
            sat_mul(m, inner, cap, overflow)
        }
        FormulaKind::Unique { domain, .. } => {
            let n = size_of(domain) as u128;
            // C(N, 2) = N*(N-1)/2；确保偶数因子先除 2，避免整除问题。
            let (a, b) = if n % 2 == 0 { (n / 2, n.saturating_sub(1)) } else { (n, n.saturating_sub(1) / 2) };
            sat_mul(a, b, cap, overflow).max(1)
        }
    }
}

/// 表达式中的除/模分母节点数（供诊断展示）。
pub fn count_divisors(e: &Expr) -> usize {
    match &e.kind {
        ExprKind::Arith { op, lhs, rhs } => {
            let self_div = if op.is_div_like() { 1 } else { 0 };
            self_div + count_divisors(lhs) + count_divisors(rhs)
        }
        ExprKind::Neg(a) | ExprKind::StrLen(a) | ExprKind::ToReal(a) | ExprKind::Bv2Int(a) => {
            count_divisors(a)
        }
        ExprKind::Int2Bv { value, .. } => count_divisors(value),
        ExprKind::Bv { lhs, rhs, .. } => count_divisors(lhs) + count_divisors(rhs),
        _ => 0,
    }
}

/// 全规范的域名 → 实例数查表。
pub fn domain_sizes(spec: &Spec) -> impl Fn(&str) -> u64 + '_ {
    move |name: &str| {
        spec.domains
            .iter()
            .find(|d| d.name == name)
            .map(|d| d.size)
            .unwrap_or(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::spec_of;
    use policylang_ast::formula::{CmpOp, Sort};
    use policylang_ast::spec::VerifyKind;
    use std::collections::BTreeMap;

    fn sizes(map: &[(&str, u64)]) -> impl Fn(&str) -> u64 {
        let m: BTreeMap<String, u64> = map.iter().map(|(a, b)| (a.to_string(), *b)).collect();
        move |n: &str| *m.get(n).unwrap_or(&0)
    }

    #[test]
    fn atomic_formula_is_one() {
        let spec = spec_of("var x: Int\nrequire R: x >= 1\n");
        let f = &spec.requires[0].formula;
        let m = measure_formula(f, &sizes(&[]), G_MAX_DEFAULT);
        assert_eq!(m.atoms_after, 1);
    }

    #[test]
    fn single_quantifier_matches_n_times_body() {
        // forall s1 in D: s1.a >= 1  ⇒ N * 1
        let spec = spec_of(
            "entity E { a: Int }\ndomain D: Set[E] [size: 100]\npolicy P { rule R: forall s in D: s.a >= 1 }\n",
        );
        let f = &spec.policies[0].rules[0].formula;
        let m = measure_formula(f, &sizes(&[("D", 100)]), G_MAX_DEFAULT);
        assert_eq!(m.atoms_after, 100);
        assert_eq!(m.atoms_before, 1);
    }

    #[test]
    fn two_var_quantifier_is_n_squared() {
        let spec = spec_of(
            "entity E { a: Int }\ndomain D: Set[E] [size: 100]\n\
             policy P { rule R: forall x, y in D: x.a >= y.a }\n",
        );
        let f = &spec.policies[0].rules[0].formula;
        let m = measure_formula(f, &sizes(&[("D", 100)]), G_MAX_DEFAULT);
        assert_eq!(m.atoms_after, 10_000);
    }

    #[test]
    fn distinct_is_falling_factorial() {
        let spec = spec_of(
            "entity E { a: Int }\ndomain D: Set[E] [size: 4]\n\
             policy P { rule R: forall x, y in D distinct: x.a != y.a }\n",
        );
        let f = &spec.policies[0].rules[0].formula;
        let m = measure_formula(f, &sizes(&[("D", 4)]), G_MAX_DEFAULT);
        assert_eq!(m.atoms_after, 12); // 4 * 3
    }

    #[test]
    fn triple_quantifier_exceeds_default_budget() {
        let spec = spec_of(
            "entity E { a: Int }\ndomain D: Set[E] [size: 100]\n\
             policy P { rule R: forall x, y, z in D: x.a + y.a >= z.a }\n",
        );
        let f = &spec.policies[0].rules[0].formula;
        // 100^3 = 10^6 恰在预算边界上（G <= G_max 仍合法）
        let m = measure_formula(f, &sizes(&[("D", 100)]), G_MAX_DEFAULT);
        assert!(!m.overflow);
        assert_eq!(m.atoms_after, G_MAX_DEFAULT);
        // 101^3 > 10^6 ⇒ 必超预算
        let m2 = measure_formula(f, &sizes(&[("D", 101)]), G_MAX_DEFAULT);
        assert!(m2.overflow);
        assert_eq!(m2.atoms_after, G_MAX_DEFAULT);
    }

    #[test]
    fn unique_costs_choose_two() {
        let spec = spec_of(
            "entity E { a: Int }\ndomain D: Set[E] [size: 8]\n\
             policy P { rule R: unique(D, a) }\n",
        );
        let f = &spec.policies[0].rules[0].formula;
        let m = measure_formula(f, &sizes(&[("D", 8)]), G_MAX_DEFAULT);
        assert_eq!(m.atoms_after, 28);
    }

    #[test]
    fn conjunction_of_quantifiers_sums() {
        let spec = spec_of(
            "entity E { a: Int }\ndomain D: Set[E] [size: 10]\n\
             policy P { rule R: (forall x in D: x.a >= 1) and (forall y in D: y.a <= 5) }\n",
        );
        let f = &spec.policies[0].rules[0].formula;
        let m = measure_formula(f, &sizes(&[("D", 10)]), G_MAX_DEFAULT);
        assert_eq!(m.atoms_after, 20);
    }

    #[test]
    fn helper_types_are_exercised() {
        let _spec = spec_of("var x: Int\nrequire R: x >= 1\n");
        let _ = VerifyKind::Consistency {
            policy: "P".into(),
        };
        let _ = Sort::Int;
        let _ = CmpOp::Ge;
    }
}
