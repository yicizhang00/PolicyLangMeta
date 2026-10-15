//! `policylang-diagnostics`（CR-6）— S-Expr 解析、模型还原、Unsat Core 归因与业务渲染。
//!
//! 管道位置：`02 §1.3` 的 ⑥ Diagnostics Translator。
//! 上游为求解器的**原始响应**；下游为治理层（`CR-7`）装配的报告。

pub mod core;
pub mod model;
pub mod render;
pub mod sexpr;

pub use core::{is_empty_carrier, minimize_core, parse_core, MinimizedCore, SubsetVerdict};
pub use model::{as_bv, as_int, extract_assignments, value_of, Assignment, Value};
pub use render::{
    attribute_core, build_counterexample, cleanup_placeholders, first_field_of, fix_template,
    format_ip, format_value,
    int_field_of, int_of, render_fix, summary_for, template_for, Counterexample, EntitySnapshot,
    FieldValue, GlobalValue, KeyRef, Remediation, RuleConflictSpan, VerdictFeature,
};
pub use sexpr::{parse_all, parse_one, SExpr};
