//! 错误码 / 告警码常量表（`04 §11`、`00 §0.2.2`）。
//!
//! 集中登记可避免各 crate 手写字符串导致的拼写漂移；`E-` 与 `W-` 命名空间以本表为准。

// ── 编译期错误（exit 3 = COMPILE_ERROR）──────────────────────────────────────
pub const E_SYNTAX: &str = "E-SYNTAX";
pub const E_BAD_HEADER: &str = "E-BAD-HEADER";
pub const E_DUP_NAME: &str = "E-DUP-NAME";
pub const E_UNKNOWN_REF: &str = "E-UNKNOWN-REF";
pub const E_SORT_MISMATCH: &str = "E-SORT-MISMATCH";
pub const E_BAD_SORT: &str = "E-BAD-SORT";
pub const E_CIDR_INVALID: &str = "E-CIDR-INVALID";
pub const E_REGEX_NONREGULAR: &str = "E-REGEX-NONREGULAR";
pub const E_REGEX_UNSUPPORTED: &str = "E-REGEX-UNSUPPORTED";
pub const E_REGEX_BUDGET: &str = "E-REGEX-BUDGET";
pub const E_REGEX_EMPTY_CLASS: &str = "E-REGEX-EMPTY-CLASS";
pub const E_NONLINEAR: &str = "E-NONLINEAR";
pub const E_GROUNDING_BUDGET: &str = "E-GROUNDING-BUDGET";
pub const E_EMPTYPOLICY: &str = "E-EMPTYPOLICY";
pub const E_NO_BRANCHES: &str = "E-NO-BRANCHES";
pub const E_MUTEX_BUDGET: &str = "E-MUTEX-BUDGET";
pub const E_MUTEX_UNKNOWN_BRANCH: &str = "E-MUTEX-UNKNOWN-BRANCH";
pub const E_CYCLIC_DECL: &str = "E-CYCLIC-DECL";
pub const E_CROSS_DOMAIN_REF: &str = "E-CROSS-DOMAIN-REF";
pub const E_DUP_LABEL: &str = "E-DUP-LABEL";
pub const E_EMPTY_CARRIER: &str = "E-EMPTY-CARRIER";
pub const E_RANGE_EMPTY: &str = "E-RANGE-EMPTY";
pub const E_WAIVER_INCOMPLETE: &str = "E-WAIVER-INCOMPLETE";
pub const E_WAIVER_SELF_APPROVE: &str = "E-WAIVER-SELF-APPROVE";
pub const E_DUP_KEY: &str = "E-DUP-KEY";
pub const E_KEY_BAD_SORT: &str = "E-KEY-BAD-SORT";
pub const E_DIV_ZERO_CONST: &str = "E-DIV-ZERO-CONST";
pub const E_VERIFY_UNKNOWN: &str = "E-VERIFY-UNKNOWN";

// ── 运行期错误（exit 4 = INTERNAL_ERROR）────────────────────────────────────
pub const E_SOLVER_MISSING: &str = "E-SOLVER-MISSING";
pub const E_SOLVER_VERSION: &str = "E-SOLVER-VERSION";
pub const E_SOLVER_PROTOCOL: &str = "E-SOLVER-PROTOCOL";
pub const E_XVALIDATE_MISMATCH: &str = "E-XVALIDATE-MISMATCH";
pub const E_REPORT_WRITE: &str = "E-REPORT-WRITE";
pub const E_INTERNAL: &str = "E-INTERNAL";
pub const E_LOGIC_UNSUPPORTED: &str = "E-LOGIC-UNSUPPORTED";
pub const E_BAD_CONFIG: &str = "E-BAD-CONFIG";
pub const E_TIMEOUT_CONFIG: &str = "E-TIMEOUT-CONFIG";

/// 已废弃别名（`00 §0.2.4`）：仅供消费方兼容匹配，**不得**在新代码中发射。
pub mod deprecated_aliases {
    /// ≡ [`super::E_XVALIDATE_MISMATCH`]
    pub const E_CROSSVAL_MISMATCH: &str = "E-CROSSVAL-MISMATCH";
    /// ≡ [`super::E_REPORT_WRITE`]
    pub const E_REPORT_IO: &str = "E-REPORT-IO";
}

// ── 告警 ────────────────────────────────────────────────────────────────────
pub const W_SHADOW: &str = "W-SHADOW";
pub const W_DUP_VAR: &str = "W-DUP-VAR";
pub const W_VACUOUS_INVARIANT: &str = "W-VACUOUS-INVARIANT";
pub const W_VACUOUS_REFINES: &str = "W-VACUOUS-REFINES";
pub const W_VACUOUS_SAFETY: &str = "W-VACUOUS-SAFETY";
pub const W_SAFETY_VACUOUS: &str = "W-SAFETY-VACUOUS";
pub const W_LOGIC_FALLBACK: &str = "W-LOGIC-FALLBACK";
pub const W_SINGLE_BACKEND: &str = "W-SINGLE-BACKEND";
pub const W_SOLVER_MISSING: &str = "W-SOLVER-MISSING";
pub const W_SOLVER_DRIFT: &str = "W-SOLVER-DRIFT";
/// UNSAT 证明未通过结构校验（`06 §6.7.2`）：该 `unsat` 不可采信。
pub const W_PROOF_CHECK_FAILED: &str = "W-PROOF-CHECK-FAILED";
pub const W_WAIVER_EXPIRED: &str = "W-WAIVER-EXPIRED";
pub const W_WAIVER_MALFORMED: &str = "W-WAIVER-MALFORMED";
pub const W_SLOW_GOAL: &str = "W-SLOW-GOAL";
pub const W_PROOF_UNAVAILABLE: &str = "W-PROOF-UNAVAILABLE";
pub const W_NONLINEAR_DIVISOR_FIXED: &str = "W-NONLINEAR-DIVISOR-FIXED";
pub const W_NONLINEAR_OPT_IN: &str = "W-NONLINEAR-OPT-IN";
pub const W_DECLARED_SORT_UNUSED: &str = "W-DECLARED-SORT-UNUSED";
