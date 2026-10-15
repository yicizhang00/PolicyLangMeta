//! 审计报告装配（`07 §7.5`、`spec/report.schema.json`）。
//!
//! 本模块的序列化结构**逐字段对齐** `spec/report.schema.json`：
//! - `additionalProperties: false` ⇒ 不得多字段；
//! - `required` 全部存在；
//! - 所有数组为**有序数组**（顺序有语义），严禁退化为 JSON 对象；
//! - 序列化遵循 JCS（键名序、无多余空白、UTF-8 无 BOM）。

use serde::{Deserialize, Serialize};

use policylang_ast::diag::Diagnostic;
use policylang_diagnostics::{Counterexample, Remediation, RuleConflictSpan};

use crate::gate::{ExitCode, GateStatus};
use crate::hashing::{self, AttestationRecord, CanonicalVerdict};

/// 报告结构版本（`00 §0.6`：`1.x` 内只增字段）。
pub const SCHEMA_VERSION: &str = "1.0";
/// 工具名与版本。
pub const TOOL_NAME: &str = "policylang";
pub const TOOL_VERSION: &str = "2.1.0";

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Tool {
    pub name: String,
    pub version: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Attestation {
    pub winner_solver: Option<String>,
    pub solver_version: Option<String>,
    pub time_ms: u64,
    pub host: String,
    pub os: String,
    pub arch: String,
}

impl Attestation {
    pub fn from_record(r: &AttestationRecord) -> Self {
        Attestation {
            winner_solver: r.winner_solver.clone(),
            solver_version: r.solver_version.clone(),
            time_ms: r.time_ms,
            host: r.host.clone(),
            os: r.os.clone(),
            arch: r.arch.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Summary {
    pub total: u64,
    pub pass: u64,
    pub fail: u64,
    pub unknown: u64,
    pub waived: u64,
    pub error: u64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct WaiverEntry {
    pub waiver_name: String,
    pub target: String,
    pub owner: String,
    pub approver: String,
    pub expires: String,
    pub reason: String,
    /// `Active` 覆盖 `Fail` 为 `Waived`；`Expired` 回退 `Fail` 并记 `W-WAIVER-EXPIRED`。
    pub state: String,
}

/// 一项检查。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Check {
    pub check_name: String,
    pub target_type: String,
    pub status: String,
    pub verdict: String,
    pub winning_solver: Option<String>,
    pub time_ms: u64,
    pub conflicting_rules: Vec<RuleConflictSpan>,
    pub counterexample: Option<Counterexample>,
    pub verdict_feature: String,
    pub remediation: Remediation,
    pub diagnostics: Vec<Diagnostic>,
    /// 是否已执行 Unsat Core 最小化（**诚实标注**，`06 §6.9`）。
    pub core_minimized: bool,
    /// `refines` 目标的四态分类（`EQUIVALENT`/`STRICT`/`WIDENED`/`INCOMPARABLE`/`UNDETERMINED`）；
    /// 非 `refines` 目标为 `null`（`06 §6.3.3`，对应 `A-16`/`C-12` 的裁决）。
    pub refinement_class: Option<String>,
    /// UNSAT 证明的**结构性校验结果**（`06 §6.7.2`）：
    /// * `None` = 未启用 `--check-proof`、非 `unsat`、或后端无 `get-proof` 能力；
    /// * `Some(true)` = Alethe 证明通过结构校验（含末步 `false`、无 `hole`、前提不悬空）；
    /// * `Some(false)` = **未通过** ⇒ 该 `unsat` 不可采信，`status` 已降级为
    ///   `UnknownReviewRequired` 并清空冲突核，同时给出 `W-PROOF-CHECK-FAILED`。
    pub proof_checked: Option<bool>,
}

impl Check {
    /// 按 `spec/report.schema.json` 的 `allOf` 约束**规范化**字段（避免生成非法报告）。
    pub fn normalize(mut self) -> Self {
        let is_fail = self.status == "Fail";
        let is_consistency = self.target_type == "consistency";
        if is_fail && is_consistency {
            // consistency 的 FAIL 用冲突核，不用反例
            self.counterexample = None;
        } else if is_fail {
            // 其余目标的 FAIL 用反例，不用冲突核
            self.conflicting_rules.clear();
        }
        if !is_fail {
            // Pass / UnknownReviewRequired / Waived ⇒ 无反例
            self.counterexample = None;
        }
        if !is_consistency {
            self.conflicting_rules.clear();
        }
        self
    }

    /// 判定事实（进入 `proof_hash`）。
    pub fn canonical_verdict(&self) -> CanonicalVerdict {
        CanonicalVerdict {
            goal_name: self.check_name.clone(),
            target_type: self.target_type.clone(),
            verdict: self.verdict.clone(),
            core_minimal: self.core_minimized,
            conflicting_labels: self
                .conflicting_rules
                .iter()
                .map(|c| c.rule_name.clone())
                .collect(),
        }
    }
}

/// 完整审计报告。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct VerificationReport {
    pub schema_version: String,
    pub report_id: String,
    pub timestamp: String,
    pub overall_status: String,
    pub exit_code: u8,
    pub logic_used: String,
    pub spec_hash: String,
    pub query_hash: String,
    pub proof_hash: String,
    pub attestation_hash: String,
    pub tool: Tool,
    pub attestation: Attestation,
    pub checks: Vec<Check>,
    pub waivers: Vec<WaiverEntry>,
    pub summary: Summary,
}

/// 报告装配参数。
#[derive(Debug, Clone)]
pub struct ReportInput {
    pub report_id: String,
    pub timestamp: String,
    pub logic_used: String,
    pub spec_hash: String,
    /// 多目标时的 `query_hash`：取各查询哈希的**有序**汇总后再哈希。
    pub query_hashes: Vec<String>,
    pub checks: Vec<Check>,
    pub waivers: Vec<WaiverEntry>,
    pub attestation: AttestationRecord,
}

impl VerificationReport {
    /// 装配报告：合并格取 `overall_status`，映射退出码，计算四哈希。
    pub fn build(input: ReportInput, compile_stage: bool) -> VerificationReport {
        let checks: Vec<Check> = input.checks.into_iter().map(Check::normalize).collect();

        let overall = GateStatus::join_all(
            checks
                .iter()
                .map(|c| GateStatus::from_wire(&c.status).unwrap_or(GateStatus::Error)),
        );
        let exit = ExitCode::from_status(overall, compile_stage);

        let query_hash = aggregate_hash(&input.query_hashes);
        let proof_hash = if checks.is_empty() {
            hashing::sha256_hex(b"no-goal")
        } else {
            let mut buf = String::new();
            for c in &checks {
                buf.push_str(&c.canonical_verdict().to_jcs());
                buf.push('\u{1e}');
            }
            hashing::proof_hash(&input.spec_hash, &query_hash, &CanonicalVerdict {
                goal_name: "<bundle>".into(),
                target_type: "bundle".into(),
                verdict: "bundle".into(),
                core_minimal: checks.iter().all(|c| c.core_minimized),
                conflicting_labels: vec![hashing::sha256_hex(buf.as_bytes())],
            })
        };
        let attestation_hash = hashing::attestation_hash(&proof_hash, &input.attestation);

        let summary = Summary {
            total: checks.len() as u64,
            pass: checks.iter().filter(|c| c.status == "Pass").count() as u64,
            fail: checks.iter().filter(|c| c.status == "Fail").count() as u64,
            unknown: checks
                .iter()
                .filter(|c| c.status == "UnknownReviewRequired")
                .count() as u64,
            waived: checks.iter().filter(|c| c.status == "Waived").count() as u64,
            error: checks.iter().filter(|c| c.status == "Error").count() as u64,
        };

        VerificationReport {
            schema_version: SCHEMA_VERSION.to_string(),
            report_id: input.report_id,
            timestamp: input.timestamp,
            overall_status: overall.as_str().to_string(),
            exit_code: exit.code() as u8,
            logic_used: input.logic_used,
            spec_hash: input.spec_hash,
            query_hash,
            proof_hash,
            attestation_hash,
            tool: Tool {
                name: TOOL_NAME.to_string(),
                version: TOOL_VERSION.to_string(),
            },
            attestation: Attestation::from_record(&input.attestation),
            checks,
            waivers: input.waivers,
            summary,
        }
    }

    /// 规范 JSON（JCS：键序由 `serde_json::Map` 的 `BTreeMap` 保证；无多余空白）。
    pub fn to_canonical_json(&self) -> String {
        match serde_json::to_value(self) {
            Ok(v) => serde_json::to_string(&v).unwrap_or_else(|_| "{}".to_string()),
            Err(_) => "{}".to_string(),
        }
    }

    /// 人类可读摘要（CLI 输出用）。
    pub fn render_text(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!(
            "overall_status = {}  exit_code = {}\n",
            self.overall_status, self.exit_code
        ));
        s.push_str(&format!(
            "logic = {}  spec = {}  query = {}\n",
            self.logic_used,
            short(&self.spec_hash),
            short(&self.query_hash)
        ));
        s.push_str(&format!(
            "proof = {}  attestation = {}\n",
            short(&self.proof_hash),
            short(&self.attestation_hash)
        ));
        for c in &self.checks {
            s.push_str(&format!(
                "  [{}] {} ({}){}  {:.0}ms  feature={}\n",
                c.status,
                c.check_name,
                c.verdict,
                c.winning_solver
                    .as_deref()
                    .map(|w| format!(" @{w}"))
                    .unwrap_or_default(),
                c.time_ms as f64,
                c.verdict_feature
            ));
            if !c.conflicting_rules.is_empty() {
                s.push_str(&format!(
                    "      核：{}\n",
                    c.conflicting_rules
                        .iter()
                        .map(|r| format!("{}（{}）", r.rule_name, r.loc()))
                        .collect::<Vec<_>>()
                        .join("、")
                ));
            }
            if let Some(ce) = &c.counterexample {
                s.push_str(&format!("      反例：{}\n", ce.summary));
            }
            s.push_str(&format!("      建议：{}\n", c.remediation.rendered));
            for d in &c.diagnostics {
                s.push_str(&format!("      {}\n", d.render()));
            }
        }
        s
    }
}

fn short(h: &str) -> String {
    h.chars().take(12).collect()
}

/// 多目标 `query_hash`：对**有序**的逐目标哈希列表再哈希。
pub fn aggregate_hash(hashes: &[String]) -> String {
    if hashes.len() == 1 {
        return hashes[0].clone();
    }
    hashing::sha256_hex(hashes.join("\u{1e}").as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(name: &str, target: &str, status: &str, verdict: &str) -> Check {
        Check {
            check_name: name.into(),
            target_type: target.into(),
            status: status.into(),
            verdict: verdict.into(),
            winning_solver: Some("z3".into()),
            time_ms: 10,
            conflicting_rules: vec![],
            counterexample: None,
            verdict_feature: "BoundaryValue".into(),
            remediation: Remediation {
                template_id: policylang_ast::diag::FixTemplateId::Fix9,
                rendered: "r".into(),
            },
            diagnostics: vec![],
            core_minimized: true,
            refinement_class: None,
            proof_checked: None,
        }
    }

    fn build(checks: Vec<Check>) -> VerificationReport {
        VerificationReport::build(
            ReportInput {
                report_id: "rpt-test".into(),
                timestamp: "2026-10-14T00:00:00Z".into(),
                logic_used: "QF_LIA".into(),
                spec_hash: "a".repeat(64),
                query_hashes: vec!["b".repeat(64)],
                checks,
                waivers: vec![],
                attestation: AttestationRecord {
                    winner_solver: Some("z3".into()),
                    solver_version: Some("4.13".into()),
                    time_ms: 10,
                    host: "h".into(),
                    os: "linux".into(),
                    arch: "x86_64".into(),
                },
            },
            false,
        )
    }

    #[test]
    fn overall_status_is_join_and_exit_code_matches() {
        let r = build(vec![
            check("A", "consistency", "Pass", "sat"),
            check("B", "invariant", "Fail", "sat"),
        ]);
        assert_eq!(r.overall_status, "Fail");
        assert_eq!(r.exit_code, 1);
        assert_eq!(r.summary.total, 2);
        assert_eq!(r.summary.pass, 1);
        assert_eq!(r.summary.fail, 1);
    }

    #[test]
    fn error_dominates_and_maps_to_3_or_4() {
        let r = build(vec![
            check("A", "consistency", "Fail", "unsat"),
            check("B", "safety", "Error", "none"),
        ]);
        assert_eq!(r.overall_status, "Error");
        assert_eq!(r.exit_code, 4);
        let r2 = VerificationReport::build(
            ReportInput {
                report_id: "x".into(),
                timestamp: "t".into(),
                logic_used: "QF_LIA".into(),
                spec_hash: "a".repeat(64),
                query_hashes: vec!["b".repeat(64)],
                checks: vec![check("B", "safety", "Error", "none")],
                waivers: vec![],
                attestation: AttestationRecord {
                    winner_solver: None,
                    solver_version: None,
                    time_ms: 0,
                    host: "h".into(),
                    os: "linux".into(),
                    arch: "x86_64".into(),
                },
            },
            true,
        );
        assert_eq!(r2.exit_code, 3);
    }

    #[test]
    fn normalize_enforces_schema_allof() {
        // Pass 不得携带反例
        let mut c = check("A", "invariant", "Pass", "unsat");
        c.counterexample = Some(policylang_diagnostics::Counterexample {
            summary: "s".into(),
            entity_snapshots: vec![],
            globals: vec![],
        });
        let c = c.normalize();
        assert!(c.counterexample.is_none());
        // 非 consistency 的 FAIL 不得携带冲突核
        let mut c2 = check("A", "invariant", "Fail", "sat");
        c2.conflicting_rules = vec![policylang_diagnostics::RuleConflictSpan {
            rule_name: "R".into(),
            start_line: 1,
            start_col: 1,
            end_line: 1,
            end_col: 1,
        }];
        assert!(c2.normalize().conflicting_rules.is_empty());
        // consistency 的 FAIL 必须有冲突核且无反例
        let mut c3 = check("A", "consistency", "Fail", "unsat");
        c3.conflicting_rules = vec![policylang_diagnostics::RuleConflictSpan {
            rule_name: "R".into(),
            start_line: 1,
            start_col: 1,
            end_line: 1,
            end_col: 1,
        }];
        let c3 = c3.normalize();
        assert_eq!(c3.conflicting_rules.len(), 1);
        assert!(c3.counterexample.is_none());
    }

    #[test]
    fn canonical_json_is_deterministic_and_has_no_whitespace() {
        let r = build(vec![check("A", "consistency", "Pass", "sat")]);
        let a = r.to_canonical_json();
        let b = build(vec![check("A", "consistency", "Pass", "sat")]).to_canonical_json();
        assert_eq!(a, b);
        assert!(!a.contains(": "));
        assert!(a.starts_with("{\"attestation\":"));
        // 必填字段齐备
        for k in [
            "schema_version",
            "report_id",
            "timestamp",
            "overall_status",
            "exit_code",
            "logic_used",
            "spec_hash",
            "query_hash",
            "proof_hash",
            "attestation_hash",
            "tool",
            "attestation",
            "checks",
            "waivers",
            "summary",
        ] {
            assert!(a.contains(&format!("\"{k}\"")), "缺少字段 {k}");
        }
    }

    #[test]
    fn aggregate_hash_is_order_sensitive() {
        let a = aggregate_hash(&["1".into(), "2".into()]);
        let b = aggregate_hash(&["2".into(), "1".into()]);
        assert_ne!(a, b);
        assert_eq!(aggregate_hash(&["x".into()]), "x");
    }
}
