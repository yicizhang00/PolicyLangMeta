//! 退出码映射（`00 §0.4.3`，`02 §2.8`）。
//!
//! 恰为 5 个取值；`Error` 进一步区分为「编译错误(3)」与「内部错误(4)」。

pub use policylang_governance::{ExitCode, GateStatus};

/// 以给定退出码结束进程。
pub fn exit_with(code: ExitCode) -> ! {
    std::process::exit(code.code())
}

/// 便捷：把 `GateStatus` 直接映射为退出码。
#[allow(dead_code)]
pub fn code_of(status: GateStatus, compile_stage: bool) -> ExitCode {
    ExitCode::from_status(status, compile_stage)
}

/// CLI 输入错误（与「验证失败」区分：属内部错误 `4`）。
pub fn usage_error(msg: &str) -> ExitCode {
    eprintln!("policylang: {msg}");
    ExitCode::InternalError
}
