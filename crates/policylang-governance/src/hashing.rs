//! 四哈希分层（`07 §7.5`、`TH-10`，修正 `A-15`）。
//!
//! ## 分层与可复算性
//! | 哈希 | 输入 | 是否可复算 | 说明 |
//! |---|---|---|---|
//! | `spec_hash` | `canon_src(.plm)` | ✅ | 源规范化：去 BOM、LF、末尾换行 |
//! | `query_hash` | `canon_smt(.smt2)` | ✅ | 同上（`CO-5` 已保证生成端规范） |
//! | `proof_hash` | `SHA256(spec)‖SHA256(query)‖canonical_verdict` | ✅ | **仅覆盖数学事实**；**排除** `winner_solver`/耗时/宿主（`07 §7.5.6`） |
//! | `attestation_hash` | `proof_hash‖JCS(attestation_record)` | ✅ | 运行元数据（法证），不影响 `proof_hash` |
//!
//! 上游 `FR-13` 把 `winning_solver` 与耗时写进「可复算」的报告字段，但竞速**天然非确定**
//! ⇒ 哈希每次运行不同，「可复算」在数学上不成立。本模块通过分层修复该缺陷。

use sha2::{Digest, Sha256};

/// SHA-256 → 小写十六进制（64 字符）。
pub fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    hex::encode(h.finalize())
}

/// `canon_src`：源文本规范化（去 BOM、统一 LF、保证末尾换行）。
pub fn canon_src(src: &str) -> String {
    let s = src.trim_start_matches('\u{feff}').replace("\r\n", "\n").replace('\r', "\n");
    if s.ends_with('\n') {
        s
    } else {
        format!("{s}\n")
    }
}

/// `canon_smt`：与 `canon_src` 同规则（`CO-5` 已要求生成端规范，此处再兜底）。
pub fn canon_smt(smt: &str) -> String {
    canon_src(smt)
}

/// `spec_hash`。
pub fn spec_hash(src: &str) -> String {
    sha256_hex(canon_src(src).as_bytes())
}

/// `query_hash`。
pub fn query_hash(smt: &str) -> String {
    sha256_hex(canon_smt(smt).as_bytes())
}

/// 生成器哈希（可选，用于区分同规范不同生成器版本的产物）。
pub fn codegen_hash(version: &str, codegen_rev: &str) -> String {
    sha256_hex(format!("{version}|{codegen_rev}").as_bytes())
}

/// **判定事实**的规范形（进入 `proof_hash` 的第三段）。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalVerdict {
    pub goal_name: String,
    pub target_type: String,
    pub verdict: String,
    pub core_minimal: bool,
    /// 判定依据的规则/分支标签（**保序**；与竞速无关，仅与数学事实相关）。
    pub conflicting_labels: Vec<String>,
}

impl CanonicalVerdict {
    /// JCS 序列化（对象键按 UTF-16 码元序；此处借用 `serde_json` 的 `BTreeMap` 语义）。
    pub fn to_jcs(&self) -> String {
        let mut m = serde_json::Map::new();
        m.insert("goal_name".into(), serde_json::Value::String(self.goal_name.clone()));
        m.insert("target_type".into(), serde_json::Value::String(self.target_type.clone()));
        m.insert("verdict".into(), serde_json::Value::String(self.verdict.clone()));
        m.insert("core_minimal".into(), serde_json::Value::Bool(self.core_minimal));
        m.insert(
            "conflicting_labels".into(),
            serde_json::Value::Array(
                self.conflicting_labels
                    .iter()
                    .map(|s| serde_json::Value::String(s.clone()))
                    .collect(),
            ),
        );
        serde_json::Value::Object(m).to_string()
    }
}

/// `proof_hash` = `SHA256( SHA256(spec) ‖ SHA256(query) ‖ canon_verdict )`。
///
/// **注意**：入参只有两级哈希与判定事实；`winner_solver`、`time_ms`、宿主信息**一律不进入**。
pub fn proof_hash(spec_hash_hex: &str, query_hash_hex: &str, verdict: &CanonicalVerdict) -> String {
    let mut buf = Vec::new();
    buf.extend_from_slice(spec_hash_hex.as_bytes());
    buf.push(0x1f); // unit separator，避免拼接歧义
    buf.extend_from_slice(query_hash_hex.as_bytes());
    buf.push(0x1f);
    buf.extend_from_slice(verdict.to_jcs().as_bytes());
    sha256_hex(&buf)
}

/// 运行证明记录（进入 `attestation_hash`，**不进入** `proof_hash`）。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AttestationRecord {
    pub winner_solver: Option<String>,
    pub solver_version: Option<String>,
    pub time_ms: u64,
    pub host: String,
    pub os: String,
    pub arch: String,
}

impl AttestationRecord {
    pub fn to_jcs(&self) -> String {
        let mut m = serde_json::Map::new();
        m.insert(
            "winner_solver".into(),
            self.winner_solver
                .clone()
                .map(serde_json::Value::String)
                .unwrap_or(serde_json::Value::Null),
        );
        m.insert(
            "solver_version".into(),
            self.solver_version
                .clone()
                .map(serde_json::Value::String)
                .unwrap_or(serde_json::Value::Null),
        );
        m.insert("time_ms".into(), serde_json::Value::Number(self.time_ms.into()));
        m.insert("host".into(), serde_json::Value::String(self.host.clone()));
        m.insert("os".into(), serde_json::Value::String(self.os.clone()));
        m.insert("arch".into(), serde_json::Value::String(self.arch.clone()));
        serde_json::Value::Object(m).to_string()
    }
}

/// `attestation_hash` = `SHA256( proof_hash ‖ JCS(attestation_record) )`。
pub fn attestation_hash(proof_hash_hex: &str, rec: &AttestationRecord) -> String {
    let mut buf = Vec::new();
    buf.extend_from_slice(proof_hash_hex.as_bytes());
    buf.push(0x1f);
    buf.extend_from_slice(rec.to_jcs().as_bytes());
    sha256_hex(&buf)
}

/// 当前宿主信息（`hostname` 缺失时使用占位符，保持确定性格式）。
pub fn host_info() -> (String, String, String) {
    let host = std::env::var("HOSTNAME")
        .or_else(|_| std::env::var("COMPUTERNAME"))
        .unwrap_or_else(|_| "unknown-host".to_string());
    let os = std::env::consts::OS.to_string();
    let arch = std::env::consts::ARCH.to_string();
    (host, os, arch)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn verdict() -> CanonicalVerdict {
        CanonicalVerdict {
            goal_name: "P::consistency::Consistency".into(),
            target_type: "consistency".into(),
            verdict: "unsat".into(),
            core_minimal: true,
            conflicting_labels: vec!["PLR__P__A".into(), "PLR__P__B".into()],
        }
    }

    #[test]
    fn spec_hash_is_stable_across_line_endings_and_bom() {
        let a = spec_hash("#lang policylang 2\nvar x: Int\n");
        let b = spec_hash("\u{feff}#lang policylang 2\r\nvar x: Int\r\n");
        let c = spec_hash("#lang policylang 2\nvar x: Int");
        assert_eq!(a, b);
        assert_eq!(a, c);
        assert_eq!(a.len(), 64);
    }

    #[test]
    fn proof_hash_excludes_solver_and_timing() {
        let v = verdict();
        let ph1 = proof_hash("s1", "q1", &v);
        let ph2 = proof_hash("s1", "q1", &v);
        assert_eq!(ph1, ph2);
        // 不同的获胜求解器/耗时不改变 proof_hash（它们不在入参中）
        let rec_a = AttestationRecord {
            winner_solver: Some("z3".into()),
            solver_version: Some("4.13".into()),
            time_ms: 12,
            host: "h".into(),
            os: "linux".into(),
            arch: "x86_64".into(),
        };
        let rec_b = AttestationRecord {
            winner_solver: Some("cvc5".into()),
            solver_version: Some("1.2".into()),
            time_ms: 999,
            ..rec_a.clone()
        };
        assert_eq!(attestation_hash(&ph1, &rec_a) == attestation_hash(&ph1, &rec_b), false);
        // 但 proof_hash 与 attestation 无关
        assert_eq!(proof_hash("s1", "q1", &v), ph1);
    }

    #[test]
    fn proof_hash_changes_with_verdict_and_labels() {
        let v = verdict();
        let mut v2 = v.clone();
        v2.verdict = "sat".into();
        assert_ne!(proof_hash("s", "q", &v), proof_hash("s", "q", &v2));
        let mut v3 = v.clone();
        v3.conflicting_labels = vec!["PLR__P__A".into()];
        assert_ne!(proof_hash("s", "q", &v), proof_hash("s", "q", &v3));
        // 标签顺序有意义（有序数组）
        let mut v4 = v.clone();
        v4.conflicting_labels = vec!["PLR__P__B".into(), "PLR__P__A".into()];
        assert_ne!(proof_hash("s", "q", &v), proof_hash("s", "q", &v4));
    }

    #[test]
    fn jcs_is_key_sorted() {
        let j = verdict().to_jcs();
        assert!(j.starts_with("{\"conflicting_labels\""), "{j}");
        assert!(j.contains("\"core_minimal\":true"));
    }
}
