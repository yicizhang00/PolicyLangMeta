//! 规范（`Spec`）与声明；逻辑足迹 `LogicProfile`（`06 §6.4.1`）。

use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

use crate::diag::{FixTemplateId, Severity};
use crate::formula::{Formula, Sort};
use crate::span::Span;

// ─────────────────────────────────────────────────────────────────────────────
// 范围约束
// ─────────────────────────────────────────────────────────────────────────────

/// 字段/变量的范围约束（`04 §3`）。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RangeConstraint {
    /// `[min: a, max: b]`，`a ≤ b`（`W3`）。
    Numeric { min: crate::formula::Rational, max: crate::formula::Rational },
    /// `[length: lo..hi]`（仅 `String`）。
    Length { lo: u64, hi: u64 },
}

// ─────────────────────────────────────────────────────────────────────────────
// 声明
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FieldDecl {
    pub name: String,
    pub sort: Sort,
    pub range: Option<RangeConstraint>,
    /// `@key` 业务主键标注（`07 §7.2.1`；文法支持为 `OQ-7` 待裁决项，实现两条路径均支持）。
    pub is_key: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EntityDecl {
    pub name: String,
    pub fields: Vec<FieldDecl>,
    pub span: Span,
}

impl EntityDecl {
    pub fn key_field(&self) -> Option<&FieldDecl> {
        self.fields.iter().find(|f| f.is_key)
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct DomainDecl {
    pub name: String,
    pub entity: String,
    pub size: u64,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct VarDecl {
    pub name: String,
    pub sort: Sort,
    pub range: Option<RangeConstraint>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RuleDecl {
    pub name: String,
    pub formula: Formula,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BranchDecl {
    pub name: String,
    pub formula: Formula,
    pub span: Span,
}

/// `mutex A, B, C`：语义为「列出的分支两两互斥」（`04 §7.5`）。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MutexDecl {
    pub names: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PolicyDecl {
    pub name: String,
    pub rules: Vec<RuleDecl>,
    pub branches: Vec<BranchDecl>,
    pub mutexes: Vec<MutexDecl>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct InvariantDecl {
    pub name: String,
    pub formula: Formula,
    pub span: Span,
}

/// `require <name>: <formula>` —— 不可豁免的强制义务（与 `waiver` 相对）。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RequireDecl {
    pub name: String,
    pub formula: Formula,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct WaiverDecl {
    pub name: String,
    pub target: String,
    pub owner: String,
    pub approver: String,
    pub expires: String,
    pub reason: String,
    pub span: Span,
}

/// 验证目标类型（`report.schema.json` 的 `TargetType` 枚举，`04 §7`）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TargetType {
    Consistency,
    Invariant,
    Refines,
    Completeness,
    Mutex,
    Safety,
}

impl TargetType {
    pub fn as_str(self) -> &'static str {
        match self {
            TargetType::Consistency => "consistency",
            TargetType::Invariant => "invariant",
            TargetType::Refines => "refines",
            TargetType::Completeness => "completeness",
            TargetType::Mutex => "mutex",
            TargetType::Safety => "safety",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VerifyKind {
    Consistency { policy: String },
    Invariant { invariant: String, policy: String },
    Refines { new_policy: String, old_policy: String },
    Completeness { policy: String },
    Safety { policy: String },
    Mutex { policy: String },
}

impl VerifyKind {
    pub fn target_type(&self) -> TargetType {
        match self {
            VerifyKind::Consistency { .. } => TargetType::Consistency,
            VerifyKind::Invariant { .. } => TargetType::Invariant,
            VerifyKind::Refines { .. } => TargetType::Refines,
            VerifyKind::Completeness { .. } => TargetType::Completeness,
            VerifyKind::Safety { .. } => TargetType::Safety,
            VerifyKind::Mutex { .. } => TargetType::Mutex,
        }
    }

    /// `check_name` 形如 `<policy>::<target_type>::<symbol>`（`report.schema.json` 的 `Check`）。
    pub fn check_name(&self) -> String {
        match self {
            VerifyKind::Consistency { policy } => format!("{policy}::consistency::Consistency"),
            VerifyKind::Invariant { invariant, policy } => {
                format!("{policy}::invariant::{invariant}")
            }
            VerifyKind::Refines {
                new_policy,
                old_policy,
            } => format!("{new_policy}::refines::{old_policy}"),
            VerifyKind::Completeness { policy } => format!("{policy}::completeness::Coverage"),
            VerifyKind::Safety { policy } => format!("{policy}::safety::DivisionTotal"),
            VerifyKind::Mutex { policy } => format!("{policy}::mutex::MutualExclusion"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct VerifyDecl {
    pub kind: VerifyKind,
    pub span: Span,
}

/// 顶层声明分类（供依赖分析与诊断定位）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DeclKind {
    Entity,
    Domain,
    Var,
    Policy,
    Invariant,
    Require,
    Waiver,
    Verify,
}

// ─────────────────────────────────────────────────────────────────────────────
// 规范
// ─────────────────────────────────────────────────────────────────────────────

/// 一个 `.plm` 源文件解析后的完整规范。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Spec {
    /// `#lang policylang <version>` 中的版本号。
    pub lang_version: u32,
    pub entities: Vec<EntityDecl>,
    pub domains: Vec<DomainDecl>,
    pub vars: Vec<VarDecl>,
    pub policies: Vec<PolicyDecl>,
    pub invariants: Vec<InvariantDecl>,
    pub requires: Vec<RequireDecl>,
    pub waivers: Vec<WaiverDecl>,
    pub verifies: Vec<VerifyDecl>,
    /// 源文件路径（用于报告与诊断）。
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_path: Option<String>,
}

impl Spec {
    pub fn empty(lang_version: u32) -> Self {
        Spec {
            lang_version,
            entities: Vec::new(),
            domains: Vec::new(),
            vars: Vec::new(),
            policies: Vec::new(),
            invariants: Vec::new(),
            requires: Vec::new(),
            waivers: Vec::new(),
            verifies: Vec::new(),
            source_path: None,
        }
    }

    pub fn find_entity(&self, name: &str) -> Option<&EntityDecl> {
        self.entities.iter().find(|e| e.name == name)
    }

    pub fn find_domain(&self, name: &str) -> Option<&DomainDecl> {
        self.domains.iter().find(|d| d.name == name)
    }

    pub fn find_var(&self, name: &str) -> Option<&VarDecl> {
        self.vars.iter().find(|v| v.name == name)
    }

    pub fn find_policy(&self, name: &str) -> Option<&PolicyDecl> {
        self.policies.iter().find(|p| p.name == name)
    }

    pub fn find_invariant(&self, name: &str) -> Option<&InvariantDecl> {
        self.invariants.iter().find(|i| i.name == name)
    }

    /// 实体 `E` 的字段声明序（声明发射确定性 `DET`，`06 §6.2.2`）。
    pub fn entity_fields(&self, entity: &str) -> Option<&[FieldDecl]> {
        self.find_entity(entity).map(|e| e.fields.as_slice())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 逻辑足迹
// ─────────────────────────────────────────────────────────────────────────────

/// 足迹违例（非空即触发 `E-NONLINEAR` / `E-REGEX-*` 等编译阻断）。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Violation {
    pub code: String,
    pub severity: Severity,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<Span>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fix_template: Option<FixTemplateId>,
}

/// 理论足迹（`06 §6.4.1`）。`uses_*` 由**排序驱动**置位（修正 `B-7`）。
#[derive(Debug, Default, Clone, PartialEq, Serialize, Deserialize)]
pub struct LogicProfile {
    pub uses_int: bool,
    pub uses_real: bool,
    pub uses_bv: bool,
    /// 确定性集合（`BTreeSet`），保证 `logic_profile.json` 可复算。
    pub bv_widths: BTreeSet<u32>,
    pub uses_string: bool,
    pub uses_regex: bool,
    pub uses_enum: bool,
    pub uses_div_const: bool,
    pub uses_mod_const: bool,
    pub nonlinear_opt_in: bool,
    pub violations: Vec<Violation>,
}

impl LogicProfile {
    /// 组合档位候选名（`06 §6.4.2` 真值表）。**候选名**须经 `ALG-3` 能力探测确认（修正 `A-14`）。
    pub fn candidate_logic(&self) -> &'static str {
        if self.nonlinear_opt_in {
            return "ALL";
        }
        match (self.uses_string, self.uses_bv, self.uses_int, self.uses_real) {
            (false, false, false, false) => "QF_UF",
            (false, false, true, false) => "QF_LIA",
            (false, false, false, true) => "QF_LRA",
            (false, false, true, true) => "QF_LIRA",
            (false, true, false, false) => "QF_BV",
            (false, true, true, false) => "QF_BVLIA",
            (false, true, false, true) => "QF_BVLRA",
            (false, true, true, true) => "QF_BVLIRA",
            (true, false, true, false) => "QF_SLIA",
            // 字串与实数/位向量无标准组合档位 ⇒ 回落 ALL（06 §6.4.2）
            (true, false, true, true) => "ALL",
            (true, true, true, false) => "ALL",
            (true, true, true, true) => "ALL",
            // 非法组合（uses_string ⇒ uses_int），由检查器保证不可达；保守回落。
            _ => "ALL",
        }
    }

    /// 是否存在**编译阻断级**违例。
    pub fn has_blocking_violation(&self) -> bool {
        self.violations.iter().any(|v| v.severity == Severity::Error)
    }

    pub fn merge_from(&mut self, other: &LogicProfile) {
        self.uses_int |= other.uses_int;
        self.uses_real |= other.uses_real;
        self.uses_bv |= other.uses_bv;
        self.bv_widths.extend(other.bv_widths.iter().copied());
        self.uses_string |= other.uses_string;
        self.uses_regex |= other.uses_regex;
        self.uses_enum |= other.uses_enum;
        self.uses_div_const |= other.uses_div_const;
        self.uses_mod_const |= other.uses_mod_const;
        self.nonlinear_opt_in |= other.nonlinear_opt_in;
        self.violations.extend(other.violations.iter().cloned());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn candidate_logic_matches_truth_table() {
        let mut p = LogicProfile {
            uses_int: true,
            ..Default::default()
        };
        assert_eq!(p.candidate_logic(), "QF_LIA");

        p.uses_real = true;
        assert_eq!(p.candidate_logic(), "QF_LIRA");

        let s = LogicProfile {
            uses_string: true,
            uses_int: true,
            ..Default::default()
        };
        assert_eq!(s.candidate_logic(), "QF_SLIA");

        let bv = LogicProfile {
            uses_bv: true,
            uses_int: true,
            ..Default::default()
        };
        assert_eq!(bv.candidate_logic(), "QF_BVLIA");

        // 串 + 实数 → 无标准组合档位 ⇒ ALL（且应有 W-LOGIC-FALLBACK 告警，由检查器发出）
        let mixed = LogicProfile {
            uses_string: true,
            uses_int: true,
            uses_real: true,
            ..Default::default()
        };
        assert_eq!(mixed.candidate_logic(), "ALL");

        let nl = LogicProfile {
            uses_int: true,
            nonlinear_opt_in: true,
            ..Default::default()
        };
        assert_eq!(nl.candidate_logic(), "ALL");
    }
}
