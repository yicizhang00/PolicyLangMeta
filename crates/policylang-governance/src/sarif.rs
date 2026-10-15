//! SARIF 2.1.0 输出（`FR-19`、`07 §7.7`，修正 `O-9`）。
//!
//! 把反例/冲突核映射为可被 GitHub Code Scanning 等平台在 PR 行内标注的结果项。
//! 结构遵循 SARIF 2.1.0 的最小子集：`version` / `$schema` / `runs[].tool.driver` /
//! `runs[].results[]`（含 `ruleId` / `level` / `message.text` / `locations[]`）。

use crate::report::VerificationReport;

/// 生成 SARIF 文本（紧凑、键序稳定）。
///
/// 覆盖的字段（`FR-19` / `07 §7.7`）：
/// * `tool.driver.rules[]`：`id` / `name` / `shortDescription` / **`fullDescription`** /
///   **`helpUri`** / **`help`** / **`defaultConfiguration`** / `properties.tags`
/// * `results[]`：`ruleId` / **`ruleIndex`** / `level` / `message.text` + **`message.markdown`** /
///   **`partialFingerprints`** / `locations[]`（`region` 含端点）/ **`relatedLocations`**（冲突对）/
///   **`fixes`**（来自 `remediation`）/ `properties`
/// * `invocations[]`：`executionSuccessful` / **`toolExecutionNotifications`** / `properties`
///
/// **未输出 `region.snippet`**：报告中不携带策略源码文本，凭空填充会失真——
/// 与 `G-8`（诚实阻断）精神一致，宁可缺字段也不产出不可信内容。
pub fn to_sarif(report: &VerificationReport) -> String {
    let mut rule_ids: Vec<String> = Vec::new();
    let mut rules: Vec<String> = Vec::new();
    let mut results: Vec<String> = Vec::new();

    for c in &report.checks {
        let rule_id = format!("policylang/{}", c.target_type);
        let level = level_of(&c.status);
        // `ruleIndex` 必须与 `rules[]` 的下标一致
        let idx = match rule_ids.iter().position(|x| x == &rule_id) {
            Some(i) => i,
            None => {
                rule_ids.push(rule_id.clone());
                rules.push(rule_json(&rule_id, &c.target_type, level));
                rule_ids.len() - 1
            }
        };

        // 主位置：优先冲突规则（有精确行列），否则反例实例，最后兜底到规范文件
        let mut locations: Vec<String> = Vec::new();
        if c.conflicting_rules.is_empty() {
            if let Some(ce) = &c.counterexample {
                for s in ce.entity_snapshots.iter().take(3) {
                    locations.push(location_json(
                        &format!("{}[{}]", s.domain, s.display_index),
                        1,
                        1,
                        None,
                    ));
                }
            }
        }
        for r in &c.conflicting_rules {
            locations.push(location_json(
                &r.rule_name,
                r.start_line,
                r.start_col,
                Some((r.end_line, r.end_col)),
            ));
        }
        if locations.is_empty() {
            locations.push(location_json("<spec>", 1, 1, None));
        }

        // 关联位置：冲突核中**其余**规则 —— 让 PR 评审同时看到冲突双方
        let mut related: Vec<String> = Vec::new();
        for (k, r) in c.conflicting_rules.iter().enumerate().skip(1) {
            let mut rs = String::new();
            rs.push_str("{\"id\":");
            rs.push_str(&(k as u32).to_string());
            rs.push_str(",\"message\":{\"text\":");
            rs.push_str(&json(&format!("冲突规则 {}", r.rule_name)));
            rs.push_str("},\"physicalLocation\":{\"artifactLocation\":{\"uri\":");
            rs.push_str(&json(&r.rule_name));
            rs.push_str("},\"region\":{\"startLine\":");
            rs.push_str(&r.start_line.max(1).to_string());
            rs.push_str(",\"startColumn\":");
            rs.push_str(&r.start_col.max(1).to_string());
            rs.push_str("}}}");
            related.push(rs);
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

        // 稳定指纹：**不含** status/时间/求解器，使同一发现跨运行可被追踪
        let fp_seed = format!(
            "policylang/v1|{}|{}|{}|{}",
            c.check_name,
            c.target_type,
            c.verdict_feature,
            c.conflicting_rules
                .first()
                .map(|r| r.rule_name.clone())
                .unwrap_or_default()
        );
        let fp = crate::hashing::sha256_hex(fp_seed.as_bytes());

        // 修复建议 → `fixes`（仅对失败/错误有意义）
        let mut fixes: Vec<String> = Vec::new();
        if c.status == "Fail" || c.status == "Error" {
            let mut fs = String::new();
            fs.push_str("{\"description\":{\"text\":");
            fs.push_str(&json(&c.remediation.rendered));
            fs.push_str("},\"artifactChanges\":[]}");
            fixes.push(fs);
        }

        let markdown = format!(
            "**{}**\n\n{}\n\n| 项 | 值 |\n|---|---|\n| 目标类型 | `{}` |\n             | 状态 | `{}` |\n| 判定 | `{}` |\n| 判定特征 | `{}` |\n| 修复建议 | {} |",
            c.check_name, text, c.target_type, c.status, c.verdict, c.verdict_feature,
            c.remediation.rendered
        );

        let mut rs = String::new();
        rs.push_str("{\"ruleId\":");
        rs.push_str(&json(&rule_id));
        rs.push_str(",\"ruleIndex\":");
        rs.push_str(&idx.to_string());
        rs.push_str(",\"level\":");
        rs.push_str(&json(level));
        rs.push_str(",\"message\":{\"text\":");
        rs.push_str(&json(&text));
        rs.push_str(",\"markdown\":");
        rs.push_str(&json(&markdown));
        rs.push('}');
        rs.push_str(",\"partialFingerprints\":{\"policylang/v1\":");
        rs.push_str(&json(&fp));
        rs.push('}');
        rs.push_str(",\"locations\":[");
        rs.push_str(&locations.join(","));
        rs.push(']');
        if !related.is_empty() {
            rs.push_str(",\"relatedLocations\":[");
            rs.push_str(&related.join(","));
            rs.push(']');
        }
        if !fixes.is_empty() {
            rs.push_str(",\"fixes\":[");
            rs.push_str(&fixes.join(","));
            rs.push(']');
        }
        rs.push_str(",\"properties\":{\"check_name\":");
        rs.push_str(&json(&c.check_name));
        rs.push_str(",\"status\":");
        rs.push_str(&json(&c.status));
        rs.push_str(",\"verdict\":");
        rs.push_str(&json(&c.verdict));
        rs.push_str(",\"verdict_feature\":");
        rs.push_str(&json(&c.verdict_feature));
        rs.push_str(",\"core_minimized\":");
        rs.push_str(if c.core_minimized { "true" } else { "false" });
        rs.push_str(",\"time_ms\":");
        rs.push_str(&c.time_ms.to_string());
        rs.push_str(",\"winning_solver\":");
        rs.push_str(
            &c.winning_solver
                .as_deref()
                .map(json)
                .unwrap_or_else(|| "null".to_string()),
        );
        rs.push_str(",\"remediation\":{\"template_id\":");
        rs.push_str(&json(&format!("{:?}", c.remediation.template_id)));
        rs.push_str(",\"rendered\":");
        rs.push_str(&json(&c.remediation.rendered));
        rs.push('}');
        if let Some(rc) = &c.refinement_class {
            rs.push_str(",\"refinement_class\":");
            rs.push_str(&json(rc));
        }
        rs.push_str(",\"proof_hash\":");
        rs.push_str(&json(&report.proof_hash));
        rs.push_str("}}");
        results.push(rs);
    }

    // 通知：把各检查携带的诊断汇总（供平台侧呈现编译期告警/错误）
    let mut notices: Vec<String> = Vec::new();
    for c in &report.checks {
        for d in &c.diagnostics {
            let mut ns = String::new();
            ns.push_str("{\"level\":");
            ns.push_str(&json(if d.is_error() { "error" } else { "warning" }));
            ns.push_str(",\"message\":{\"text\":");
            ns.push_str(&json(&d.message));
            ns.push_str("},\"descriptor\":{\"id\":");
            ns.push_str(&json(&d.code));
            ns.push_str("},\"properties\":{\"check_name\":");
            ns.push_str(&json(&c.check_name));
            ns.push_str("}}");
            notices.push(ns);
        }
    }

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
    out.push_str(",\"toolExecutionNotifications\":[");
    out.push_str(&notices.join(","));
    out.push_str("],\"properties\":{\"overall_status\":");
    out.push_str(&json(&report.overall_status));
    out.push_str(",\"exit_code\":");
    out.push_str(&report.exit_code.to_string());
    out.push_str(",\"spec_hash\":");
    out.push_str(&json(&report.spec_hash));
    out.push_str(",\"query_hash\":");
    out.push_str(&json(&report.query_hash));
    out.push_str(",\"proof_hash\":");
    out.push_str(&json(&report.proof_hash));
    out.push_str("}}],\"results\":[");
    out.push_str(&results.join(","));
    out.push_str("]}]}");
    out
}

/// `GateStatus` → SARIF `level`。
fn level_of(status: &str) -> &'static str {
    match status {
        "Fail" | "Error" => "error",
        "UnknownReviewRequired" => "warning",
        "Waived" => "note",
        _ => "none",
    }
}

fn rule_json(rule_id: &str, target_type: &str, level: &str) -> String {
    let mut s = String::new();
    s.push_str("{\"id\":");
    s.push_str(&json(rule_id));
    s.push_str(",\"name\":");
    s.push_str(&json(&snake(target_type)));
    s.push_str(",\"shortDescription\":{\"text\":");
    s.push_str(&json(&format!("PolicyLang {target_type} 检查")));
    s.push('}');
    s.push_str(",\"fullDescription\":{\"text\":");
    s.push_str(&json(&full_desc(target_type)));
    s.push('}');
    s.push_str(",\"helpUri\":");
    s.push_str(&json(&format!("https://policylang.dev/rules/{target_type}")));
    s.push_str(",\"help\":{\"text\":");
    s.push_str(&json(&help_text(target_type)));
    s.push('}');
    s.push_str(",\"defaultConfiguration\":{\"level\":");
    s.push_str(&json(level));
    s.push('}');
    // 注意：末尾需 **两层** `}`——一层收 `properties`，一层收规则对象本身
    s.push_str(",\"properties\":{\"tags\":[\"policylang\",\"formal-verification\"]}}");
    s
}

/// 规则长描述（`target_type` 的语义，取自 `06 §6.3` 的六式目标）。
fn full_desc(t: &str) -> String {
    match t {
        "consistency" => "策略集自洽性：存在满足全部规则的输入（π ≜ ∃m ∈ M. R_P(m)）。",
        "invariant" => "安全不变量：不变量在所有满足规则的输入下成立（Γ ⟹ Inv）。",
        "refines" => "策略精化对比：新策略是否被旧策略包含（双查询四态：EQUIVALENT/STRICT/WIDENED/INCOMPARABLE）。",
        "completeness" => "分支完备性：各分支的并集覆盖整个输入空间。",
        "mutex" => "分支两两互斥：任意两分支不可同时成立。",
        "safety" => "除法全域性：所有除法的除数在义务集内非零（避免求解器未指定语义导致的假证明）。",
        _ => "PolicyLang 验证目标。",
    }
    .to_string()
}

fn help_text(t: &str) -> String {
    format!("见 docs/06-SMT编码与求解编排规范.md §6.3 的 `{t}` 编码；修复建议见 docs/07 §7.4。")
}

fn location_json(artifact: &str, line: u32, col: u32, end: Option<(u32, u32)>) -> String {
    let mut s = String::new();
    s.push_str("{\"physicalLocation\":{\"artifactLocation\":{\"uri\":");
    s.push_str(&json(artifact));
    s.push_str("},\"region\":{\"startLine\":");
    s.push_str(&line.max(1).to_string());
    s.push_str(",\"startColumn\":");
    s.push_str(&col.max(1).to_string());
    if let Some((el, ec)) = end {
        if el > 0 {
            s.push_str(",\"endLine\":");
            s.push_str(&el.to_string());
        }
        if ec > 0 {
            s.push_str(",\"endColumn\":");
            s.push_str(&ec.to_string());
        }
    }
    s.push_str("}}}");
    s
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
    #[test]
    fn sarif_result_carries_fingerprint_fixes_and_rule_index() {
        let r = report_with(vec![Check {
            check_name: "P::invariant::I".into(),
            target_type: "invariant".into(),
            status: "Fail".into(),
            verdict: "sat".into(),
            winning_solver: Some("cvc5".into()),
            time_ms: 3,
            conflicting_rules: vec![],
            counterexample: Some(Counterexample {
                summary: "越界".into(),
                entity_snapshots: vec![],
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
        // 必须是**合法 JSON**（历史缺陷：`rules[]` 少一层 `}` 导致整份 SARIF 非法）
        let v: serde_json::Value = serde_json::from_str(&s).expect("SARIF 必须是合法 JSON");
        let run = &v["runs"][0];
        let rule = &run["tool"]["driver"]["rules"][0];
        assert!(rule.get("fullDescription").is_some(), "{s}");
        assert!(rule.get("helpUri").is_some(), "{s}");
        assert!(rule.get("help").is_some(), "{s}");
        assert_eq!(rule["defaultConfiguration"]["level"], "error");
        assert!(rule["properties"]["tags"].is_array());

        let res = &run["results"][0];
        assert_eq!(res["ruleIndex"], 0);
        assert_eq!(res["level"], "error");
        assert!(res["message"]["markdown"].is_string(), "{s}");
        assert!(res["partialFingerprints"]["policylang/v1"].is_string(), "{s}");
        assert!(res["fixes"].is_array(), "Fail 应带修复建议");
        assert!(res["locations"].is_array());
    }

    #[test]
    fn sarif_fingerprint_is_stable_and_excludes_status() {
        // 同一发现跨运行必须得到同一指纹（否则平台会把同一问题当作新问题重复报）
        let mk = |status: &str| Check {
            check_name: "P::mutex::A_B".into(),
            target_type: "mutex".into(),
            status: status.into(),
            verdict: "unsat".into(),
            winning_solver: None,
            time_ms: 1,
            conflicting_rules: vec![],
            counterexample: None,
            verdict_feature: "MutexOverlap".into(),
            remediation: Remediation {
                template_id: policylang_ast::diag::FixTemplateId::Fix1,
                rendered: "x".into(),
            },
            diagnostics: vec![],
            core_minimized: true,
            refinement_class: None,
        };
        let a: serde_json::Value = serde_json::from_str(&to_sarif(&report_with(vec![mk("Pass")]))).unwrap();
        let b: serde_json::Value = serde_json::from_str(&to_sarif(&report_with(vec![mk("Fail")]))).unwrap();
        let fa = a["runs"][0]["results"][0]["partialFingerprints"]["policylang/v1"].clone();
        let fb = b["runs"][0]["results"][0]["partialFingerprints"]["policylang/v1"].clone();
        assert_eq!(fa, fb, "指纹不得随 status 变化");
    }

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
                        range: None,
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
