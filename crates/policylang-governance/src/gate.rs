//! 状态合并格与退出码映射（`00 §0.4.2`/`§0.4.3`，修正 `B-15`/`B-16`）。
//!
//! 状态恰为 5 个；合并格 `Error ⊐ Fail ⊙ UnknownReviewRequired ⊐ Waived ⊐ Pass`。
//! 退出码恰为 5 个：`0`（Pass/Waived）/ `1`（Fail）/ `2`（UnknownReviewRequired）/
//! `3`（编译错误）/ `4`（内部错误）。

use serde::{Deserialize, Serialize};

/// 单项检查状态（= `GateStatus`，`00 §0.4.1`）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum GateStatus {
    /// 严重度 0（最低）。
    Pass,
    Waived,
    UnknownReviewRequired,
    Fail,
    /// 严重度 4（最高）。
    Error,
}

impl GateStatus {
    pub fn as_str(self) -> &'static str {
        match self {
            GateStatus::Pass => "Pass",
            GateStatus::Waived => "Waived",
            GateStatus::UnknownReviewRequired => "UnknownReviewRequired",
            GateStatus::Fail => "Fail",
            GateStatus::Error => "Error",
        }
    }

    /// 合并格 join：取严重度较高者（`Error ⊐ Fail ⊐ UnknownReviewRequired ⊐ Waived ⊐ Pass`）。
    pub fn join(self, other: GateStatus) -> GateStatus {
        self.max(other)
    }

    pub fn join_all<I: IntoIterator<Item = GateStatus>>(it: I) -> GateStatus {
        it.into_iter().fold(GateStatus::Pass, GateStatus::join)
    }

    pub fn from_wire(s: &str) -> Option<GateStatus> {
        match s {
            "Pass" => Some(GateStatus::Pass),
            "Waived" => Some(GateStatus::Waived),
            "UnknownReviewRequired" => Some(GateStatus::UnknownReviewRequired),
            "Fail" => Some(GateStatus::Fail),
            "Error" => Some(GateStatus::Error),
            _ => None,
        }
    }
}

/// CLI 退出码（`00 §0.4.3`）。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExitCode {
    Pass = 0,
    Fail = 1,
    Unknown = 2,
    CompileError = 3,
    InternalError = 4,
}

impl ExitCode {
    pub fn code(self) -> i32 {
        self as i32
    }

    /// `status` → 退出码。`Error` 需区分「编译错误(3)」与「内部错误(4)」。
    pub fn from_status(status: GateStatus, compile_stage: bool) -> ExitCode {
        match status {
            GateStatus::Pass | GateStatus::Waived => ExitCode::Pass,
            GateStatus::Fail => ExitCode::Fail,
            GateStatus::UnknownReviewRequired => ExitCode::Unknown,
            GateStatus::Error => {
                if compile_stage {
                    ExitCode::CompileError
                } else {
                    ExitCode::InternalError
                }
            }
        }
    }

    pub fn from_code(c: i32) -> Option<ExitCode> {
        match c {
            0 => Some(ExitCode::Pass),
            1 => Some(ExitCode::Fail),
            2 => Some(ExitCode::Unknown),
            3 => Some(ExitCode::CompileError),
            4 => Some(ExitCode::InternalError),
            _ => None,
        }
    }
}

/// CI 门禁决策（`07 §7.7` 的五分支映射）。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateDecision {
    /// 继续（`Pass` / `Waived`）。
    Allow,
    /// 阻断（`Fail`）。
    Block,
    /// 转人工（`UnknownReviewRequired`）。
    Escalate,
    /// 工具链故障（`Error`）。
    ToolFailure,
}

pub fn decide(status: GateStatus) -> GateDecision {
    match status {
        GateStatus::Pass | GateStatus::Waived => GateDecision::Allow,
        GateStatus::Fail => GateDecision::Block,
        GateStatus::UnknownReviewRequired => GateDecision::Escalate,
        GateStatus::Error => GateDecision::ToolFailure,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn join_is_a_max_by_severity() {
        use GateStatus::*;
        assert_eq!(Pass.join(Fail), Fail);
        assert_eq!(Waived.join(UnknownReviewRequired), UnknownReviewRequired);
        assert_eq!(Fail.join(Error), Error);
        assert_eq!(Pass.join(Pass), Pass);
        assert_eq!(join_all_of(vec![Pass, Waived, Pass]), Waived);
        assert_eq!(join_all_of(vec![Pass, UnknownReviewRequired, Waived]), UnknownReviewRequired);
        assert_eq!(join_all_of(vec![Fail, Error, Pass]), Error);
    }

    fn join_all_of(v: Vec<GateStatus>) -> GateStatus {
        GateStatus::join_all(v)
    }

    #[test]
    fn exit_codes_cover_five_values() {
        assert_eq!(ExitCode::from_status(GateStatus::Pass, false).code(), 0);
        assert_eq!(ExitCode::from_status(GateStatus::Waived, false).code(), 0);
        assert_eq!(ExitCode::from_status(GateStatus::Fail, false).code(), 1);
        assert_eq!(
            ExitCode::from_status(GateStatus::UnknownReviewRequired, false).code(),
            2
        );
        assert_eq!(ExitCode::from_status(GateStatus::Error, true).code(), 3);
        assert_eq!(ExitCode::from_status(GateStatus::Error, false).code(), 4);
        // 恰 5 个取值
        for c in 0..=4 {
            assert!(ExitCode::from_code(c).is_some());
        }
        assert!(ExitCode::from_code(5).is_none());
    }

    #[test]
    fn gate_decision_matches_five_branches() {
        assert_eq!(decide(GateStatus::Pass), GateDecision::Allow);
        assert_eq!(decide(GateStatus::Waived), GateDecision::Allow);
        assert_eq!(decide(GateStatus::Fail), GateDecision::Block);
        assert_eq!(decide(GateStatus::UnknownReviewRequired), GateDecision::Escalate);
        assert_eq!(decide(GateStatus::Error), GateDecision::ToolFailure);
    }

    #[test]
    fn from_wire_roundtrip() {
        for s in [
            GateStatus::Pass,
            GateStatus::Waived,
            GateStatus::UnknownReviewRequired,
            GateStatus::Fail,
            GateStatus::Error,
        ] {
            assert_eq!(GateStatus::from_wire(s.as_str()), Some(s));
        }
        assert_eq!(GateStatus::from_wire("OK"), None);
    }
}
