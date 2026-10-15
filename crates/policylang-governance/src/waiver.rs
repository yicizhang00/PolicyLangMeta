//! 豁免（Waiver）机制（`FR-18`、`07 §7.9`，修正 `O-4`/`O-14`）。
//!
//! 语义：`Active` 且未过期的豁免把对应检查的 `Fail` **覆盖为 `Waived`**（退出码 `0`）；
//! 已过期则**回退 `Fail`** 并记录 `W-WAIVER-EXPIRED`（限时例外必须真的到期）。

use policylang_ast::codes::W_WAIVER_EXPIRED;
use policylang_ast::diag::Diagnostic;
use policylang_ast::spec::WaiverDecl;
use policylang_ast::Span;

use crate::report::{Check, WaiverEntry};

/// 当前 UTC 日期（`YYYY-MM-DD`），由系统时钟推导。
pub fn today_iso() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);
    let days = secs.div_euclid(86_400);
    civil_from_days(days)
}

/// Howard Hinnant 的 `civil_from_days`（无外部依赖的历法换算）。
fn civil_from_days(z: i64) -> String {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = (z - era * 146_097) as i64; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365; // [0, 399]
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let d = doy - (153 * mp + 2) / 5 + 1; // [1, 31]
    let m = if mp < 10 { mp + 3 } else { mp - 9 }; // [1, 12]
    let y = if m <= 2 { y + 1 } else { y };
    format!("{y:04}-{m:02}-{d:02}")
}

/// 判断豁免状态：`expires < today` ⇒ `Expired`（ISO-8601 日期可直接按字典序比较）。
pub fn waiver_state(expires: &str, today: &str) -> &'static str {
    if expires.trim() < today {
        "Expired"
    } else {
        "Active"
    }
}

/// 判断豁免的 `target` 是否命中某项检查。
///
/// 命中规则（确定性，`07 §7.9.2`）：`target` 等于 `check_name`，或等于其前缀策略名
/// （`<policy>::…` 的第一段），或等于核中的规则名。
pub fn targets(check: &Check, target: &str) -> bool {
    if check.check_name == target {
        return true;
    }
    let policy = check.check_name.split("::").next().unwrap_or("");
    if policy == target {
        return true;
    }
    check
        .conflicting_rules
        .iter()
        .any(|r| r.rule_name == target)
}

/// 豁免应用结果。
#[derive(Debug, Clone)]
pub struct WaiverOutcome {
    pub entries: Vec<WaiverEntry>,
    pub diagnostics: Vec<Diagnostic>,
    /// 实际把哪些检查从 `Fail` 覆盖为 `Waived`。
    pub covered: Vec<(String, String)>,
}

/// 应用全部豁免：更新检查状态、生成报告条目与诊断。
pub fn apply(checks: &mut [Check], waivers: &[WaiverDecl], today: &str) -> WaiverOutcome {
    let mut entries = Vec::new();
    let mut diagnostics = Vec::new();
    let mut covered = Vec::new();

    for w in waivers {
        let state = waiver_state(&w.expires, today);
        entries.push(WaiverEntry {
            waiver_name: w.name.clone(),
            target: w.target.clone(),
            owner: w.owner.clone(),
            approver: w.approver.clone(),
            expires: w.expires.clone(),
            reason: w.reason.clone(),
            state: state.to_string(),
        });
        if state == "Expired" {
            diagnostics.push(
                Diagnostic::warning(
                    W_WAIVER_EXPIRED,
                    format!(
                        "豁免 `{}` 已于 {} 到期（今日 {}）：对应检查回退为 `Fail`，\
                         请续期或修复根因（07 §7.9.4）",
                        w.name, w.expires, today
                    ),
                )
                .with_span(w.span),
            );
            continue;
        }
        for c in checks.iter_mut() {
            if targets(c, &w.target) && c.status == "Fail" {
                c.status = "Waived".to_string();
                covered.push((c.check_name.clone(), w.name.clone()));
            }
        }
    }

    // 报告条目按声明顺序（waivers 已保序）
    WaiverOutcome {
        entries,
        diagnostics,
        covered,
    }
}

/// 空豁免集合（无豁免时的默认结果）。
pub fn empty_span() -> Span {
    Span::default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use policylang_ast::diag::FixTemplateId;

    fn check(name: &str, status: &str) -> Check {
        Check {
            check_name: name.into(),
            target_type: "consistency".into(),
            status: status.into(),
            verdict: "unsat".into(),
            winning_solver: None,
            time_ms: 0,
            conflicting_rules: vec![],
            counterexample: None,
            verdict_feature: "ConflictingBoundPair".into(),
            remediation: policylang_diagnostics::Remediation {
                template_id: FixTemplateId::Fix4,
                rendered: "r".into(),
            },
            diagnostics: vec![],
            core_minimized: false,
            refinement_class: None,
        }
    }

    fn waiver(name: &str, target: &str, expires: &str) -> WaiverDecl {
        WaiverDecl {
            name: name.into(),
            target: target.into(),
            owner: "alice".into(),
            approver: "bob".into(),
            expires: expires.into(),
            reason: "pending".into(),
            span: Span::default(),
        }
    }

    #[test]
    fn civil_date_conversion() {
        assert_eq!(civil_from_days(0), "1970-01-01");
        assert_eq!(civil_from_days(19_000), "2022-01-08");
        assert!(today_iso().len() == 10);
    }

    #[test]
    fn active_waiver_covers_fail() {
        let mut checks = vec![check("P::consistency::Consistency", "Fail")];
        let out = apply(&mut checks, &[waiver("W1", "P", "2099-01-01")], "2026-10-14");
        assert_eq!(checks[0].status, "Waived");
        assert_eq!(out.entries[0].state, "Active");
        assert_eq!(out.covered.len(), 1);
        assert!(out.diagnostics.is_empty());
    }

    #[test]
    fn expired_waiver_falls_back_to_fail_with_warning() {
        let mut checks = vec![check("P::consistency::Consistency", "Fail")];
        let out = apply(&mut checks, &[waiver("W1", "P", "2020-01-01")], "2026-10-14");
        assert_eq!(checks[0].status, "Fail");
        assert_eq!(out.entries[0].state, "Expired");
        assert_eq!(out.diagnostics.len(), 1);
        assert_eq!(out.diagnostics[0].code, W_WAIVER_EXPIRED);
    }

    #[test]
    fn non_matching_target_does_not_cover() {
        let mut checks = vec![check("P::consistency::Consistency", "Fail")];
        apply(&mut checks, &[waiver("W1", "Other", "2099-01-01")], "2026-10-14");
        assert_eq!(checks[0].status, "Fail");
    }

    #[test]
    fn pass_is_not_touched() {
        let mut checks = vec![check("P::consistency::Consistency", "Pass")];
        let out = apply(&mut checks, &[waiver("W1", "P", "2099-01-01")], "2026-10-14");
        assert_eq!(checks[0].status, "Pass");
        assert!(out.covered.is_empty());
    }
}
