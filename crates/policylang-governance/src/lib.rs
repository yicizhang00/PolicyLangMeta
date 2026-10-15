//! `policylang-governance`（CR-7）— 审计报告、四哈希分层、SARIF、Waiver 与 CI 门禁退出码。
//!
//! 管道位置：`02 §1.3` 的 ⑦ Governance & CI Gate。

pub mod gate;
pub mod hashing;
pub mod report;
pub mod sarif;
pub mod waiver;

pub use gate::{decide, ExitCode, GateDecision, GateStatus};
pub use hashing::{
    attestation_hash, canon_smt, canon_src, codegen_hash, host_info, proof_hash, query_hash,
    sha256_hex, spec_hash, AttestationRecord, CanonicalVerdict,
};
pub use report::{
    aggregate_hash, Attestation, Check, ReportInput, Summary, Tool, VerificationReport,
    WaiverEntry, SCHEMA_VERSION, TOOL_NAME, TOOL_VERSION,
};
pub use sarif::to_sarif;
pub use waiver::{apply as apply_waivers, today_iso, targets as waiver_targets, WaiverOutcome};

/// 报告 ID：`rpt-<UTC 时间戳>-<短随机>`（不参与任何哈希）。
pub fn new_report_id(stamp: &str) -> String {
    // 用当前时间的纳秒位作为短随机源，避免引入 rand 依赖
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.subsec_nanos())
        .unwrap_or(0);
    let tag = format!("{:08x}", nanos & 0xffff_ffff);
    format!("rpt-{stamp}-{}", &tag[..4])
}

/// UTC 时间戳（RFC 3339，秒精度；由系统时钟推导，无外部依赖）。
pub fn now_rfc3339() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);
    let days = secs.div_euclid(86_400);
    let rem = secs.rem_euclid(86_400);
    let date = {
        let z = days + 719_468;
        let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
        let doe = z - era * 146_097;
        let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365;
        let y = yoe + era * 400;
        let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
        let mp = (5 * doy + 2) / 153;
        let d = doy - (153 * mp + 2) / 5 + 1;
        let m = if mp < 10 { mp + 3 } else { mp - 9 };
        let y = if m <= 2 { y + 1 } else { y };
        (y, m, d)
    };
    format!(
        "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z",
        date.0,
        date.1,
        date.2,
        rem / 3600,
        (rem % 3600) / 60,
        rem % 60
    )
}

/// 时间戳形如 `20261014T000000Z`（用于报告 ID）。
pub fn stamp_compact(rfc3339: &str) -> String {
    rfc3339.replace(['-', ':'], "").replace('+', "")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rfc3339_and_stamp_are_well_formed() {
        let t = now_rfc3339();
        assert!(t.ends_with('Z'));
        assert_eq!(t.len(), 20, "{t}");
        let s = stamp_compact(&t);
        assert!(!s.contains('-'));
        assert!(!s.contains(':'));
        let id = new_report_id(&s);
        assert!(id.starts_with("rpt-"));
    }
}
