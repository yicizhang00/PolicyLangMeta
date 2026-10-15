//! SARIF 2.1.0 输出（`FR-19`、`07 §7.7`，修正 `O-9`）。
//!
//! 把反例/冲突核映射为可被 GitHub Code Scanning 等平台在 PR 行内标注的结果项。
//! 结构遵循 SARIF 2.1.0 的最小子集：`version` / `$schema` / `runs[].tool.driver` /
//! `runs[].results[]`（含 `ruleId` / `level` / `message.text` / `locations[]`）。

use crate::report::VerificationReport;

/// 生成 SARIF 文本（JCS 风格：紧凑、键序稳定）。
pub fn to_sarif(report: &VerificationReport) -> String {
    let mut rules: Vec<String> = Vec::new();
    let mut rule_ids: Vec<String> = Vec::new();
    let mut results: Vec<String> = Vec::new();

    for c in &report.checks {
        let rule_id = format!("policylang/{}", c.target_type);
        if !rule_ids.contains(&rule_id) {
            rule_ids.push(rule_id.clone());
            rules.push(format!(
                "{{\"id\":{},\"name\":{},\"shortDescription\":{{\"text\":{}}},\
\"helpUri\":\"https://policylang.dev/rules/{}\"}}",
                json(&rule_id),
                json(&snake(&c.target_type)),
                json(&format!("PolicyLang {} 检查", c.target_type)),
                c.target_type
            ));
        }

        let level = match c.status.as_str() {
            "Fail" => "error",
            "Error" => "error",
            "UnknownReviewRequired" => "warning",
            "Waived" => "note",
            _ => "none",
        };

        // 反例优先映射到具体实例字段；否则映射到冲突规则的规则名行
        let mut locations: Vec<String> = Vec::new();
        if let Some(ce) = &c.counterexample {
            if let Some(s) = ce.entity_snapshots.first() {
                locations.push(location_json(
                    &format!("{}[{}]", s.domain, s.display_index),
                    1,
                    1,
                ));
            }
        }
        for r in &c.conflicting_rules {
            locations.push(location_json(&r.rule_name, r.start_line, r.start_col));
        }
        if locations.is_empty() {
            locations.push(location_json("<spec>", 1, 1));
        }

        let text = if let Some(ce) = &c.counterexample {
            ce.summary.clone()
        } else if !c.conflicting_rules.is_empty() {
            format!(
                "冲突核：{}",
                c.conflicting_rules
                    .iter()
                    .map(|r| format!("{}（{}）", r.rule_name, r.loc()))
                    .collect::<Vec<_>>()
                    .join("、")
            )
        } else {
            format!("{}：{}（{}）", c.status, c.check_name, c.verdict)
        };

        results.push(format!(
            "{{\"ruleId\":{},\"level\":{},\"message\":{{\"text\":{}}},\
\"properties\":{{\"check_name\":{},\"status\":{},\"verdict\":{},\"verdict_feature\":{},\
\"remediation\":{},\"proof_hash\":{}}},\"locations\":[{}]}}",
            json(&rule_id),
            json(level),
            json(&text),
            json(&c.check_name),
            json(&c.status),
            json(&c.verdict),
            json(&c.verdict_feature),
            json(&c.remediation.rendered),
            json(&report.proof_hash),
            locations.join(",")
        ));
    }

    // 用显式拼接避免 `format!` 的花括号转义（更可读、更不易错）
    let mut out = String::new();
    out.push_str("{\"$schema\":\"https://json.schemastore.org/sarif-2.1.0.json\",");
    out.push_str("\"version\":\"2.1.0\",\"runs\":[");
    out.push_str("{\"tool\":{\"driver\":{\"name\":");
    out.push_str(&json("policylang"));
    out.push_str(",\"version\":");
    out.push_str(&json(&report.tool.version));
    out.push_str(",\"informationUri\":\"https://policylang.dev\",\"rules\":[");
    out.push_str(&rules.join(","));
    out.push_str("]}},");
    out.push_str("\"invocations\":[{\"executionSuccessful\":");
    out.push_str(if report.exit_code == 0 { "true" } else { "false" });
    out.push_str(",\"properties\":{\"overall_status\":");
    out.push_str(&json(&report.overall_status));
    out.push_str(",\"exit_code\":");
    out.push_str(&report.exit_code.to_string());
    out.push_str(",\"spec_hash\":");
    out.push_str(&json(&report.spec_hash));
    out.push_str(",\"proof_hash\":");
    out.push_str(&json(&report.proof_hash));
    out.push_str("}}],\"results\":[");
    out.push_str(&results.join(","));
    out.push_str("]}]}");
    out
}

fn location_json(artifact: &str, line: u32, col: u32) -> String {
    format!(
        "{{\"physicalLocation\":{{\"artifactLocation\":{{\"uri\":{}}},\
\"region\":{{\"startLine\":{},\"startColumn\":{}}}}}}}",
        json(artifact),
        line.max(1),
        col.max(1)
    )
}

fn snake(s: &str) -> String {
    s.to_string()
}

fn json(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::report::*;
    use policylang_diagnostics::{Counterexample, EntitySnapshot, FieldValue, Remediation};

    fn report_with(checks: Vec<Check>) -> VerificationReport {
        VerificationReport::build(
            ReportInput {
                report_id: "r".into(),
                timestamp: "t".into(),
                logic_used: "QF_LIA".into(),
                spec_hash: "a".repeat(64),
                query_hashes: vec!["b".repeat(64)],
                checks,
                waivers: vec![],
                attestation: crate::hashing::AttestationRecord {
                    winner_solver: Some("z3".into()),
                    solver_version: Some("4.13".into()),
                    time_ms: 1,
                    host: "h".into(),
                    os: "linux".into(),
                    arch: "x86_64".into(),
                },
            },
            false,
        )
    }

    #[test]
    fn sarif_has_required_shape() {
        let r = report_with(vec![Check {
            check_name: "P::invariant::I".into(),
            target_type: "invariant".into(),
            status: "Fail".into(),
            verdict: "sat".into(),
            winning_solver: Some("cvc5".into()),
            time_ms: 3,
            conflicting_rules: vec![],
            counterexample: Some(Counterexample {
                summary: "Services[3] 越界".into(),
                entity_snapshots: vec![EntitySnapshot {
                    domain: "Services".into(),
                    entity: "Service".into(),
                    internal_index: 2,
                    display_index: 3,
                    primary_key: None,
                    fields: vec![FieldValue {
                        name: "host_ip".into(),
                        sort: "IPv4".into(),
                        value: "10.0.2.9".into(),
                    }],
                }],
                globals: vec![],
            }),
            verdict_feature: "OutOfSubnet".into(),
            remediation: Remediation {
                template_id: policylang_ast::diag::FixTemplateId::Fix3,
                rendered: "调整网段".into(),
            },
            diagnostics: vec![],
            core_minimized: false,
            refinement_class: None,
        }]);
        let s = to_sarif(&r);
        assert!(s.contains("\"version\":\"2.1.0\""));
        assert!(s.contains("\"ruleId\":\"policylang/invariant\""));
        assert!(s.contains("\"level\":\"error\""));
        assert!(s.contains("\"startLine\":1"));
        assert!(s.contains("\"executionSuccessful\":false"));
        // JSON 可解析
        let v: serde_json::Value = serde_json::from_str(&s).expect("SARIF 必须是合法 JSON");
        assert_eq!(v["version"], "2.1.0");
    }

    #[test]
    fn pass_yields_none_level() {
        let r = report_with(vec![Check {
            check_name: "P::consistency::C".into(),
            target_type: "consistency".into(),
            status: "Pass".into(),
            verdict: "sat".into(),
            winning_solver: None,
            time_ms: 0,
            conflicting_rules: vec![],
            counterexample: None,
            verdict_feature: "BoundaryValue".into(),
            remediation: Remediation {
                template_id: policylang_ast::diag::FixTemplateId::Fix9,
                rendered: "n/a".into(),
            },
            diagnostics: vec![],
            core_minimized: true,
            refinement_class: None,
        }]);
        let s = to_sarif(&r);
        assert!(s.contains("\"level\":\"none\""));
        assert!(s.contains("\"executionSuccessful\":true"));
    }
}
