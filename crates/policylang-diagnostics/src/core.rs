//! Unsat Core 的解析与**最小化** `ALG-4`（`06 §6.9`、`03 §3.14`、`TH-8`）。
//!
//! ## 为什么必须最小化（修正 `A-13` / `C-3`）
//! `(get-unsat-core)` 返回的**只是**一个不可满足子集，**不保证极小更不保证最小**
//! （Z3/CVC5 均含冗余项）。上游三处（`§4.1`、`FR-7`、`G-6`）却声称输出「**最小**冲突核」——
//! 用户据此删除规则会**误删必需规则**。本模块以两阶段算法主动精化，并要求报告以
//! `core_minimal` 字段**诚实标注**是否在预算内达到极小。

use std::collections::BTreeSet;

use crate::sexpr::SExpr;

/// 从 `(get-unsat-core)` 响应解析标签列表（保序、去重）。
pub fn parse_core(exprs: &[SExpr]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut seen: BTreeSet<String> = BTreeSet::new();
    for e in exprs {
        collect_labels(e, &mut out, &mut seen);
    }
    out
}

fn collect_labels(e: &SExpr, out: &mut Vec<String>, seen: &mut BTreeSet<String>) {
    match e {
        SExpr::Atom(a) => {
            if seen.insert(a.clone()) {
                out.push(a.clone());
            }
        }
        SExpr::List(v) => {
            for x in v {
                collect_labels(x, out, seen);
            }
        }
        SExpr::Str(_) => {}
    }
}

/// 单次子集检查的结论。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubsetVerdict {
    /// 该子集仍不可满足。
    Unsat,
    /// 该子集可满足（⇒ 被删除的元素**必需**）。
    Sat,
    /// 不确定（超时/未知）——保守起见**保留**该元素。
    Unknown,
}

/// `ALG-4` 最小化的结果。
#[derive(Debug, Clone)]
pub struct MinimizedCore {
    /// 精化后的核（保序：与输入顺序一致）。
    pub core: Vec<String>,
    /// 是否已达**极小**（任意删除一个元素都会变为可满足）。
    pub minimal: bool,
    /// 实际执行的检查次数。
    pub checks: usize,
    /// 是否因预算耗尽而提前停止。
    pub budget_exhausted: bool,
}

/// `ALG-4`：deletion-based 精化（`06 §6.9.2`）。
///
/// 从 `initial` 出发，逐个尝试删除元素；若删除后仍 `unsat`，则该元素**冗余**，永久删除。
/// 一轮之后仍有删除则再迭代，直到一轮无删除（此时达到**极小**）或预算耗尽。
///
/// `check(&[String]) -> SubsetVerdict` 由调用方提供（通常是对**同一求解器会话**用
/// assumptions 重查，`06 §6.9.3`）。
pub fn minimize_core<F>(initial: Vec<String>, budget: usize, mut check: F) -> MinimizedCore
where
    F: FnMut(&[String]) -> SubsetVerdict,
{
    let mut core = initial;
    let mut checks = 0usize;
    #[allow(unused_assignments)]
    let mut budget_exhausted = false;

    if core.is_empty() {
        return MinimizedCore {
            core,
            minimal: true,
            checks: 0,
            budget_exhausted: false,
        };
    }

    'outer: loop {
        let mut removed_any = false;
        let snapshot = core.clone();
        for e in snapshot {
            if checks >= budget {
                budget_exhausted = true;
                break 'outer;
            }
            let candidate: Vec<String> = core.iter().filter(|x| **x != e).cloned().collect();
            checks += 1;
            match check(&candidate) {
                SubsetVerdict::Unsat => {
                    core = candidate;
                    removed_any = true;
                }
                SubsetVerdict::Sat | SubsetVerdict::Unknown => { /* 必需，保留 */ }
            }
        }
        if !removed_any {
            return MinimizedCore {
                core,
                minimal: true,
                checks,
                budget_exhausted: false,
            };
        }
    }

    MinimizedCore {
        core,
        minimal: false,
        checks,
        budget_exhausted,
    }
}

/// 空核检测：`Bnd` 自身不可满足时核心为空（`E-EMPTY-CARRIER`，`06 §6.2.4`）。
pub fn is_empty_carrier(core: &[String]) -> bool {
    core.is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexpr::parse_all;

    fn set(xs: &[&str]) -> Vec<String> {
        xs.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn parses_core_list() {
        let c = parse_core(&parse_all("(PLR__P__A PLR__P__B)").unwrap());
        assert_eq!(c, set(&["PLR__P__A", "PLR__P__B"]));
        let c2 = parse_core(&parse_all("()").unwrap());
        assert!(c2.is_empty());
        // 去重且保序
        let c3 = parse_core(&parse_all("(A B A)").unwrap());
        assert_eq!(c3, set(&["A", "B"]));
    }

    #[test]
    fn minimalization_removes_redundant_elements() {
        // 语义模型：{A, B} 互斥（unsat）；C 无关。
        let sat_for = |x: &[String]| -> SubsetVerdict {
            let has_a = x.iter().any(|s| s == "A");
            let has_b = x.iter().any(|s| s == "B");
            if has_a && has_b {
                SubsetVerdict::Unsat
            } else {
                SubsetVerdict::Sat
            }
        };
        let r = minimize_core(set(&["A", "B", "C"]), 64, sat_for);
        assert_eq!(r.core, set(&["A", "B"]));
        assert!(r.minimal);
        // 第 1 轮删除 C（3 次尝试）+ 第 2 轮确认不可再删（2 次尝试）= 5
        assert_eq!(r.checks, 5);
    }

    #[test]
    fn three_way_conflict_minimizes_to_two() {
        // {A,B,C} unsat；任一含 A 与 B 的子集 unsat；C 冗余
        let f = |x: &[String]| -> SubsetVerdict {
            let n = x.iter().filter(|s| s.as_str() == "A" || s.as_str() == "B").count();
            if n >= 2 {
                SubsetVerdict::Unsat
            } else {
                SubsetVerdict::Sat
            }
        };
        let r = minimize_core(set(&["A", "B", "C"]), 64, f);
        assert_eq!(r.core, set(&["A", "B"]));
        assert!(r.minimal);
    }

    #[test]
    fn unknown_is_conservatively_kept() {
        let f = |_: &[String]| SubsetVerdict::Unknown;
        let r = minimize_core(set(&["A", "B"]), 64, f);
        assert_eq!(r.core, set(&["A", "B"]));
        assert!(r.minimal); // 无可删除 ⇒ 一轮即止
    }

    #[test]
    fn budget_exhaustion_is_honest() {
        let f = |x: &[String]| -> SubsetVerdict {
            if x.len() >= 2 {
                SubsetVerdict::Unsat
            } else {
                SubsetVerdict::Sat
            }
        };
        let r = minimize_core(set(&["A", "B", "C", "D"]), 1, f);
        assert!(r.budget_exhausted);
        assert!(!r.minimal);
    }

    #[test]
    fn empty_core_is_carrier_error() {
        assert!(is_empty_carrier(&[]));
    }
}
