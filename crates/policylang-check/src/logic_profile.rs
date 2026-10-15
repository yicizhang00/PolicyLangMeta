//! 理论足迹 `LogicProfile` 的**排序驱动置位**（`06 §6.4.1`，修正 `B-7`）。
//!
//! 上游 `LogicProfile` **没有任何把 `uses_*` 置位的语句**，导致 `deduce_smt_logic()`
//! 恒返回 `ALL`、理论路由完全失效。本模块把置位规则集中于此，由 `typecheck` 的遍历调用，
//! 保证「一处定义、无遗漏」。

use policylang_ast::codes::W_LOGIC_FALLBACK;
use policylang_ast::diag::Diagnostic;
use policylang_ast::formula::Sort;
use policylang_ast::spec::LogicProfile;

/// 按排序置位（`06 §6.4.1` 赋值规则表）。
pub fn mark_sort(p: &mut LogicProfile, s: &Sort) {
    match s {
        Sort::Int => p.uses_int = true,
        Sort::Real => {
            p.uses_real = true;
            p.uses_int = true;
        }
        Sort::Bool => {}
        Sort::Str => {
            // `str.len : Int` ⇒ 串必然蕴含整数（06 §6.4.2 的 12 种可达组合之依据）
            p.uses_string = true;
            p.uses_int = true;
        }
        Sort::Bv(w) => {
            p.uses_bv = true;
            p.bv_widths.insert(*w);
        }
        Sort::Enum(_) => {
            // Enum 采用有界整数编码（DD-6.2）⇒ 计入 uses_int
            p.uses_enum = true;
            p.uses_int = true;
        }
    }
}

/// `matches_all` ⇒ `uses_regex` + `uses_string` + `uses_int`。
pub fn mark_regex(p: &mut LogicProfile) {
    p.uses_regex = true;
    p.uses_string = true;
    p.uses_int = true;
}

/// 常量除数的 `div` / `mod`。
pub fn mark_div_const(p: &mut LogicProfile, is_mod: bool) {
    if is_mod {
        p.uses_mod_const = true;
    } else {
        p.uses_div_const = true;
    }
    p.uses_int = true;
}

/// `to_real` ⇒ `uses_real` + `uses_int`。
pub fn mark_to_real(p: &mut LogicProfile) {
    p.uses_real = true;
    p.uses_int = true;
}

/// 组合档位回落告警 `W-LOGIC-FALLBACK`（`06 §6.4.2`）。
///
/// 仅当回落**并非**由 `nonlinear_opt_in` 引起时报出（后者应改报 `E-NONLINEAR` / `UNKNOWN_RISK`）。
pub fn fallback_warning(scope_name: &str, p: &LogicProfile) -> Option<Diagnostic> {
    if p.candidate_logic() == "ALL" && !p.nonlinear_opt_in {
        let reason = if p.uses_string && p.uses_real {
            "字串与实数无标准组合档位"
        } else if p.uses_string && p.uses_bv {
            "字串与位向量无标准组合档位"
        } else {
            "该理论组合无标准档位名"
        };
        return Some(Diagnostic::warning(
            W_LOGIC_FALLBACK,
            format!(
                "`{scope_name}` 的逻辑档位回落为 `ALL`（{reason}）；档位名仅作**候选**，\
                 实际以 ALG-3 运行期能力探测为准（06 §6.4.3）"
            ),
        ));
    }
    None
}

/// 汇总一组公式足迹（`LogicProfile::merge_from` 的便捷包装）。
pub fn merge_all(profiles: &[LogicProfile]) -> LogicProfile {
    let mut p = LogicProfile::default();
    for x in profiles {
        p.merge_from(x);
    }
    p
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sort_marks_are_driven_by_sort() {
        let mut p = LogicProfile::default();
        mark_sort(&mut p, &Sort::Str);
        assert!(p.uses_string && p.uses_int && !p.uses_real);
        mark_sort(&mut p, &Sort::Real);
        assert!(p.uses_real);
        mark_sort(&mut p, &Sort::Bv(128));
        assert!(p.uses_bv && p.bv_widths.contains(&128));
        mark_sort(&mut p, &Sort::Enum(vec!["A".into()]));
        assert!(p.uses_enum && p.uses_int);
    }

    #[test]
    fn fallback_warning_only_for_unsupported_combos() {
        let mut p = LogicProfile {
            uses_string: true,
            uses_int: true,
            uses_real: true,
            ..Default::default()
        };
        assert!(fallback_warning("P", &p).is_some());
        p.uses_real = false;
        assert!(fallback_warning("P", &p).is_none()); // QF_SLIA 有标准档位
        let nl = LogicProfile {
            uses_int: true,
            nonlinear_opt_in: true,
            ..Default::default()
        };
        assert!(fallback_warning("P", &nl).is_none());
    }
}
