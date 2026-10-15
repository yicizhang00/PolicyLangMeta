//! `policylang-ast`（CR-2）— 强类型抽象语法、排序系统与展平命名。
//!
//! 对应文档：`02 §2.1`（职责与公开 API）、`05 §3`（AST 定义）、
//! `03 §3.2`（排序与语义模型）、`03 §3.2.4`（展平命名）、`00 §0.6`。
//!
//! 本 crate 是**全部 crate 的公共数据契约**，不依赖任何其他 policylang crate（`INV-L1` 层序单向）。
//!
//! ## 关键设计
//! - `Rational { num: i128, den: i128 }` 取代上游 `f64`（修正 `C-6`），保证 `Real` 的精确有理数语义；
//! - `FormulaKind::And/Or` 采用**列表形式**，与 Lean 侧右结合二元 `conj`/`disj` 同构（`12 §12.5.1`）；
//! - `scalar_symbol` 为**单一实现**（`INV-L2`），`codegen` 的声明发射与其**复用同一函数**（修正 `A-7`）。

pub mod codes;
pub mod diag;
pub mod formula;
pub mod naming;
pub mod spec;
pub mod span;

pub use diag::{ensure_no_errors, Diagnostic, FixTemplateId, Severity};
pub use formula::{
    smt_string_literal, ArithOp, Atom, BvOp, Cidr, CmpOp, Expr, ExprKind, Formula, FormulaKind,
    Rational, RegLan, Sort,
};
pub use spec::{
    BranchDecl, DeclKind, DomainDecl, EntityDecl, FieldDecl, InvariantDecl, LogicProfile,
    MutexDecl, PolicyDecl, RangeConstraint, RequireDecl, RuleDecl, Spec, TargetType, VarDecl,
    VerifyDecl, VerifyKind, Violation, WaiverDecl,
};
pub use span::Span;
