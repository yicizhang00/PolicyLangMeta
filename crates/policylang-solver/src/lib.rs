//! `policylang-solver`（CR-5）— 理论感知路由、进程级竞速编排、响应流解析、交叉验证、能力探测。
//!
//! 管道位置：`02 §1.3` 的 ⑤ Theory-Aware Orchestra。
//!
//! ## 与规范的一处实现层等价替换（诚实说明）
//! `DD-4` 指定 tokio 的 `JoinSet::shutdown().await` + `kill_on_drop`。本实现改用
//! `std::thread` + `std::process::Child` 并**显式** `kill()` + `wait()`；两者在
//! 「首胜立即强杀其余且残留为 0」（`FR-8` / `NFR-3` / `AC-5`）上**行为等价**，
//! 差别仅在于不引入异步运行时（本环境无法离线获取其 `rt-multi-thread` 依赖）。

pub mod crossval;
pub mod discover;
pub mod interval;
pub mod invocation;
pub mod lockfile;
pub mod orchestra;
pub mod probe;
pub mod proofcheck;
pub mod response;
pub mod router;

pub use crossval::{eval_formula, reglan_full_match, replay, Replay};
pub use discover::{base_name, default_roots, ENV_SEARCH_PATH};
pub use interval::{build_interval_script, interval_from_objectives};
pub use proofcheck::{asserted_forms, build_proof_script, check_alethe, extract_proof, ProofCheck};
pub use invocation::{proof_hint, stdin_argv};
pub use lockfile::{
    excluded_backends, is_blocking, normalize_version, sha256_file, verify_lock, Drift, DriftKind,
    LockEntry, LockFile, LOCK_VERSION,
};
pub use orchestra::{
    extract_named_label, kill_and_reap, rebuild_script, run_captured, run_captured_argv, solve_race,
    split_named_asserts, Backend, Confirmation, ProcResult, RaceOptions, RaceOutcome, SolverRun,
};
pub use probe::{capability_json, probe_all, probe_backend, Capability, CANDIDATE_LOGICS};
pub use response::{
    is_expected_mismatch, parse_responses, ParsedOutput, Response, Verdict,
};
pub use router::{route, Route, RouteOptions, BASELINE_MATRIX};

use std::time::Duration;

/// 按默认名称发现后端（`z3` / `cvc5` / `bitwuzla`）。
///
/// 解析每个后端的**绝对可执行路径**（`PATH` → `POLICYLANG_SOLVER_PATH` → 用户级默认安装根，
/// 见 [`discover`] 模块）；未找到时回退为裸可执行名，使「缺失」以启动失败的形式
/// 暴露给 `ALG-3` 探测。
pub fn discover_backends() -> Vec<Backend> {
    discover::discover()
}

/// 便捷：探测 + 路由。
pub fn prepare(
    candidate_logic: &str,
    backends: &[Backend],
    probe_timeout: Duration,
    route_opts: &RouteOptions,
) -> (Vec<Capability>, Route) {
    let caps = probe_all(backends, probe_timeout);
    let r = route(candidate_logic, &caps, route_opts);
    (caps, r)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn discovery_lists_three_known_backends() {
        let b = discover_backends();
        assert_eq!(b.len(), 3);
        assert_eq!(b[0].name, "z3");
    }

    #[test]
    fn prepare_survives_missing_solvers() {
        // 本环境可能未安装任何求解器：必须优雅降级而非 panic
        let (caps, r) = prepare(
            "QF_LIA",
            &discover_backends(),
            Duration::from_millis(60),
            &RouteOptions::default(),
        );
        assert_eq!(caps.len(), 3);
        // 无论是否安装，路由都不应 panic；未安装时为空路由
        let _ = r.is_empty();
    }
}
