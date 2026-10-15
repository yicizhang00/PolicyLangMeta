//! 反例还原、`FIX-*` 修复建议与业务可读渲染（`07 §7.2`–`§7.4`）。
//!
//! 设计要点：
//! - **确定性**：同一 `(规范, 判定, 模型)` 必须产生逐字节相同的字符串（`07 §7.2.4`），
//!   故所有文案**表驱动**、无自由文本拼接（修正 `B-18` 的「不可复算」问题）；
//! - **保序**：`entity_snapshots` 按 `internal_index` 升序、`fields` 按字段声明序
//!   （`spec/report.schema.json` 要求有序数组）。

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use policylang_ast::diag::FixTemplateId;
use policylang_ast::formula::{Rational, Sort};
use policylang_ast::spec::Spec;
use policylang_ast::Span;

use crate::model::{as_bv, as_int, Assignment, Value};

/// 反例特征名（与 `spec/report.schema.json` 的 `VerdictFeature` 枚举逐字一致）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum VerdictFeature {
    SameHostPortConflict,
    DbInstanceDivergence,
    OutOfSubnet,
    ConflictingBoundPair,
    RangeWidened,
    UncoveredRegion,
    MutexOverlap,
    DenominatorZero,
    BoundaryValue,
    Timeout,
    UnknownRiskLogic,
    EmptyCore,
    NonlinearConstruct,
    GroundingBudgetExceeded,
    SolverUnavailable,
    CrossvalMismatch,
}

impl VerdictFeature {
    pub fn as_str(self) -> &'static str {
        match self {
            VerdictFeature::SameHostPortConflict => "SameHostPortConflict",
            VerdictFeature::DbInstanceDivergence => "DbInstanceDivergence",
            VerdictFeature::OutOfSubnet => "OutOfSubnet",
            VerdictFeature::ConflictingBoundPair => "ConflictingBoundPair",
            VerdictFeature::RangeWidened => "RangeWidened",
            VerdictFeature::UncoveredRegion => "UncoveredRegion",
            VerdictFeature::MutexOverlap => "MutexOverlap",
            VerdictFeature::DenominatorZero => "DenominatorZero",
            VerdictFeature::BoundaryValue => "BoundaryValue",
            VerdictFeature::Timeout => "Timeout",
            VerdictFeature::UnknownRiskLogic => "UnknownRiskLogic",
            VerdictFeature::EmptyCore => "EmptyCore",
            VerdictFeature::NonlinearConstruct => "NonlinearConstruct",
            VerdictFeature::GroundingBudgetExceeded => "GroundingBudgetExceeded",
            VerdictFeature::SolverUnavailable => "SolverUnavailable",
            VerdictFeature::CrossvalMismatch => "CrossvalMismatch",
        }
    }
}

/// 业务主键引用。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct KeyRef {
    pub field: String,
    pub value: String,
}

/// 字段值（`value` 为已按 `07 §7.2.2` 格式化的确定性字符串）。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FieldValue {
    pub name: String,
    pub sort: String,
    pub value: String,
    /// 反例区间化（`06 §6.3.7`）：该字段在**保持违规成立**前提下的可自由变动区间。
    /// `None` = 未启用、不适用（非连续排序）、或后端不支持 Optimize（`f_optimize = false`）。
    #[serde(skip_serializing_if = "Option::is_none")]
    pub range: Option<FieldRange>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct GlobalValue {
    pub name: String,
    pub sort: String,
    pub value: String,
    /// 见 [`FieldValue::range`]。
    #[serde(skip_serializing_if = "Option::is_none")]
    pub range: Option<FieldRange>,
}

/// 「保持违规成立」的自由变动区间（`06 §6.3.7`）。
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldRange {
    /// 下界（SMT-LIB2 字面量文本，如 `80` / `(- 5)` / `(/ 7 2)`）。
    pub lo: String,
    /// 上界（同上）。
    pub hi: String,
}

impl FieldRange {
    /// 单点区间（`lo == hi`）也应呈现为区间，以便读者明确「此处确实无自由度」。
    pub fn is_point(&self) -> bool {
        self.lo == self.hi
    }
}

/// 一个域实例的快照。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EntitySnapshot {
    pub domain: String,
    pub entity: String,
    /// SMT 内部索引 `i ∈ Fin N`（0 起）。
    pub internal_index: usize,
    /// 业务显示编号 `k = i + 1`（1 起，`07 §7.2.1`）。
    pub display_index: usize,
    /// `@key` 存在时为业务主键，否则 `null`。
    pub primary_key: Option<KeyRef>,
    pub fields: Vec<FieldValue>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Counterexample {
    pub summary: String,
    pub entity_snapshots: Vec<EntitySnapshot>,
    pub globals: Vec<GlobalValue>,
}

/// 冲突核归因（`07 §7.3.2`）。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RuleConflictSpan {
    pub rule_name: String,
    pub start_line: u32,
    pub start_col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

impl RuleConflictSpan {
    pub fn from_span(rule_name: &str, s: Span) -> Self {
        RuleConflictSpan {
            rule_name: rule_name.to_string(),
            start_line: s.start_line,
            start_col: s.start_col,
            end_line: s.end_line,
            end_col: s.end_col,
        }
    }

    pub fn loc(&self) -> String {
        format!("{}:{}", self.start_line, self.start_col)
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Remediation {
    pub template_id: FixTemplateId,
    pub rendered: String,
}

// ═════════════════════════════════════════════════════════════════════════════
// 值格式化（确定性，07 §7.2.2）
// ═════════════════════════════════════════════════════════════════════════════

/// 按排序格式化一个值。`Enum` 由成员名还原（`DD-6.2` 的整数编码反向映射）。
pub fn format_value(v: &Value, sort: &Sort) -> String {
    match (v, sort) {
        // 枚举：整数编码 ⇒ 成员名
        (Value::Int(i), Sort::Enum(members)) => members
            .get(*i as usize)
            .cloned()
            .unwrap_or_else(|| format!("<out-of-range enum {i}>")),
        (Value::Int(i), _) => i.to_string(),
        (Value::Real(r), _) => format_rational(r),
        (Value::Bool(b), _) => b.to_string(),
        (Value::Str(s), _) => s.clone(),
        (Value::Bv(x, _), Sort::Bv(32)) => format_ip(*x, 32),
        (Value::Bv(x, _), Sort::Bv(128)) => format_ip(*x, 128),
        (Value::Bv(x, _), _) => x.to_string(),
        (Value::Unknown(s), _) => s.clone(),
    }
}

fn format_rational(r: &Rational) -> String {
    if r.den == 1 {
        r.num.to_string()
    } else {
        format!("{}/{}", r.num, r.den)
    }
}

/// IPv4 点分十进制 / IPv6 冒号分组。
pub fn format_ip(v: u128, width: u32) -> String {
    if width == 32 {
        format!(
            "{}.{}.{}.{}",
            (v >> 24) & 0xff,
            (v >> 16) & 0xff,
            (v >> 8) & 0xff,
            v & 0xff
        )
    } else {
        (0..8)
            .map(|i| format!("{:x}", (v >> (112 - 16 * i)) & 0xffff))
            .collect::<Vec<_>>()
            .join(":")
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// 反例与核归因
// ═════════════════════════════════════════════════════════════════════════════

/// 还原反例：按 `domains` 指定的域（保序）展开全部实例快照 + 全局变量。
///
/// `summary` 由调用方给出（确定性判定），避免自由文本破坏可复算性。
pub fn build_counterexample(
    spec: &Spec,
    domains: &[String],
    assignment: &Assignment,
    summary: String,
) -> Counterexample {
    use policylang_ast::naming::{global_symbol, scalar_symbol};

    let mut entity_snapshots = Vec::new();
    for dname in domains {
        let Some(d) = spec.find_domain(dname) else {
            continue;
        };
        let Some(ent) = spec.find_entity(&d.entity) else {
            continue;
        };
        let key_field = ent.key_field().map(|f| f.name.clone());
        for i in 0..d.size as usize {
            let mut fields = Vec::with_capacity(ent.fields.len());
            for f in &ent.fields {
                let sym = scalar_symbol(dname, i, &f.name);
                let val = assignment
                    .get(&sym)
                    .map(|v| format_value(v, &f.sort))
                    .unwrap_or_else(|| "?".to_string());
                fields.push(FieldValue {
                    name: f.name.clone(),
                    sort: f.sort.display_name().to_string(),
                    value: val,
                    range: None,
                });
            }
            let primary_key = key_field.as_ref().and_then(|k| {
                let f = ent.fields.iter().find(|x| &x.name == k)?;
                let sym = scalar_symbol(dname, i, k);
                let v = assignment.get(&sym)?;
                Some(KeyRef {
                    field: k.clone(),
                    value: format_value(v, &f.sort),
                })
            });
            entity_snapshots.push(EntitySnapshot {
                domain: dname.clone(),
                entity: d.entity.clone(),
                internal_index: i,
                display_index: i + 1,
                primary_key,
                fields,
            });
        }
    }

    let globals = spec
        .vars
        .iter()
        .map(|v| GlobalValue {
            name: v.name.clone(),
            sort: v.sort.display_name().to_string(),
            range: None,
            value: assignment
                .get(&global_symbol(&v.name))
                .map(|x| format_value(x, &v.sort))
                .unwrap_or_else(|| "?".to_string()),
        })
        .collect();

    Counterexample {
        summary,
        entity_snapshots,
        globals,
    }
}

/// 把 Unsat Core 的标签**归因**回 DSL 规则名 + 源码跨度（按 `start_line` 升序）。
///
/// `labels`：(标签, 展示名, 源码跨度)。未命中的标签原样保留为 `rule_name`（不静默丢弃）。
pub fn attribute_core(core: &[String], labels: &[(String, String, Span)]) -> Vec<RuleConflictSpan> {
    let map: BTreeMap<&str, (&str, Span)> = labels
        .iter()
        .map(|(l, n, s)| (l.as_str(), (n.as_str(), *s)))
        .collect();
    let mut out: Vec<RuleConflictSpan> = core
        .iter()
        .map(|l| match map.get(l.as_str()) {
            Some((name, span)) => RuleConflictSpan::from_span(name, *span),
            None => RuleConflictSpan {
                rule_name: l.clone(),
                start_line: 1,
                start_col: 1,
                end_line: 1,
                end_col: 1,
            },
        })
        .collect();
    out.sort_by_key(|x| (x.start_line, x.start_col, x.rule_name.clone()));
    out.dedup_by(|a, b| a.rule_name == b.rule_name && a.start_line == b.start_line);
    out
}

/// 业务可读摘要（**确定性**：由可勾选条件拼装，无自由文本）。
pub fn summary_for(
    target_type: &str,
    feature: VerdictFeature,
    conflict: &[RuleConflictSpan],
    counterexample: Option<&Counterexample>,
) -> String {
    let head = match feature {
        VerdictFeature::SameHostPortConflict => "同一宿主机上存在端口冲突",
        VerdictFeature::DbInstanceDivergence => "使用数据库的服务未指向同一数据库实例",
        VerdictFeature::OutOfSubnet => "存在超出受控网段的主机",
        VerdictFeature::ConflictingBoundPair => "存在互斥的上下界规则对",
        VerdictFeature::RangeWidened => "新策略扩大了合法输入范围",
        VerdictFeature::UncoveredRegion => "存在未被任何分支覆盖的输入死区",
        VerdictFeature::MutexOverlap => "存在同时命中两个互斥分支的输入",
        VerdictFeature::DenominatorZero => "存在使分母为 0 的输入",
        VerdictFeature::BoundaryValue => "判定落在边界值上",
        VerdictFeature::Timeout => "求解超时，判定不确定",
        VerdictFeature::UnknownRiskLogic => "逻辑档位不可判定，判定不确定",
        VerdictFeature::EmptyCore => "约束载体自身不可满足（空核）",
        VerdictFeature::NonlinearConstruct => "含非线性构造，超出可判定片段",
        VerdictFeature::GroundingBudgetExceeded => "展开规模超出预算",
        VerdictFeature::SolverUnavailable => "所需求解器不可用",
        VerdictFeature::CrossvalMismatch => "交叉验证结果不一致",
    };
    let mut s = format!("[{target_type}] {head}");
    if !conflict.is_empty() {
        s.push_str("；冲突规则：");
        s.push_str(
            &conflict
                .iter()
                .map(|c| format!("{}（{}）", c.rule_name, c.loc()))
                .collect::<Vec<_>>()
                .join("、"),
        );
    }
    if let Some(ce) = counterexample {
        if let Some(first) = ce.entity_snapshots.first() {
            s.push_str(&format!(
                "；实例 {}{}",
                first.domain,
                match &first.primary_key {
                    Some(k) => format!("[{}]", k.value),
                    None => format!("[{}]", first.display_index),
                }
            ));
        }
        if !ce.globals.is_empty() {
            let g: Vec<String> = ce
                .globals
                .iter()
                .filter(|x| x.value != "?")
                .map(|x| format!("{}={}", x.name, x.value))
                .collect();
            if !g.is_empty() {
                s.push_str(&format!("；全局：{}", g.join(", ")));
            }
        }
    }
    s
}

// ═════════════════════════════════════════════════════════════════════════════
// FIX-* 修复模板（表驱动，07 §7.4.2）
// ═════════════════════════════════════════════════════════════════════════════

/// 模板原文；`{name}` 为占位符。
pub fn fix_template(id: FixTemplateId) -> &'static str {
    match id {
        FixTemplateId::Fix1 => "调整 {entity} 的 {field}（当前 {value}）以消除同主机端口冲突",
        FixTemplateId::Fix2 => "统一 {entity} 的 {field}（当前 {value}）使其指向同一数据库实例",
        FixTemplateId::Fix3 => "将 {entity} 的 {field}（当前 {value}）调整至网段 {expected} 内",
        FixTemplateId::Fix4 => "规则 {rule_a}（{loc_a}）与 {rule_b}（{loc_b}）的上下界互斥；放宽其一或将交集纳入合法域",
        FixTemplateId::Fix5 => "新策略将 {field} 的下界由 {expected} 放宽为 {value}，扩大了暴露面；请恢复原下界或显式豁免",
        FixTemplateId::Fix6 => "分支未覆盖 {field} 的 [{lo}, {hi}] 区间；请新增分支或放宽相邻分支边界",
        FixTemplateId::Fix7 => "分支 {branch_a} 与 {branch_b} 在 {value} 处同时命中；请收紧其边界使二者互斥",
        FixTemplateId::Fix8 => "分母 {field} 可能取 0（当前 {value}）；请增加 {field} != 0 的前提约束",
        FixTemplateId::Fix9 => "{field} 的判定落在边界值 {value}；请确认边界语义（闭/开区间）",
        FixTemplateId::Fix10 => "求解超时（{elapsed_ms} ms > {timeout_ms} ms）；可放宽容差、缩小域规模或提高 --timeout",
        FixTemplateId::Fix11 => "逻辑档位 {logic} 不可判定；请拆分理论（分离位向量与整数子查询）或减少字符串/实数混用",
        FixTemplateId::Fix12 => "约束载体（Bnd）自身不可满足：字段 {field} 的取值范围与其类型/其它约束冲突，请修正声明",
        FixTemplateId::Fix13 => "表达式 {expr} 为非线性（乘/除两侧皆非常量）；请改为常量系数，或改写为可线性化形式",
        FixTemplateId::Fix14 => "展开规模超出预算（{actual} > {budget}）；请减小域 size、减少量词变量数或使用 distinct",
        FixTemplateId::Fix15 => "求解器 {solver} 不可用（{detail}）；请安装对应版本或调整 --solvers",
        FixTemplateId::Fix16 => "交叉验证不一致：{solver_a} 判定 {verdict_a}，{solver_b} 判定 {verdict_b}；请核查规范或调整后端集合",
    }
}

/// 用占位符渲染模板（**纯函数** ⇒ `proof_hash` 稳定）。
pub fn render_fix(id: FixTemplateId, vars: &[(&str, &str)]) -> String {
    let mut out = fix_template(id).to_string();
    for (k, v) in vars {
        out = out.replace(&format!("{{{k}}}"), v);
    }
    cleanup_placeholders(&out)
}

/// 确定性消解**未填**的占位符：`{name}` → `n/a`。
///
/// 必要性：`07 §7.2.4` 要求修复建议可复算；若残留 `{…}` 会让报告出现「看起来像模板未生效」
/// 的字符串，且不同调用方填充不一致会破坏确定性。此处统一为固定占位符 `n/a`。
pub fn cleanup_placeholders(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0usize;
    while i < chars.len() {
        if chars[i] == '{' {
            if let Some(end) = chars[i + 1..].iter().position(|c| *c == '}') {
                let body: String = chars[i + 1..i + 1 + end].iter().collect();
                // 仅替换形如 `{标识符}` 的占位符，避免误伤正常文本中的花括号
                if !body.is_empty()
                    && body
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_')
                {
                    out.push_str("n/a");
                    i += end + 2;
                    continue;
                }
            }
        }
        out.push(chars[i]);
        i += 1;
    }
    out
}

/// 依 `(目标类型, 特征)` 选择修复模板（确定性映射，`07 §7.4.1`）。
pub fn template_for(feature: VerdictFeature) -> FixTemplateId {
    match feature {
        VerdictFeature::SameHostPortConflict => FixTemplateId::Fix1,
        VerdictFeature::DbInstanceDivergence => FixTemplateId::Fix2,
        VerdictFeature::OutOfSubnet => FixTemplateId::Fix3,
        VerdictFeature::ConflictingBoundPair => FixTemplateId::Fix4,
        VerdictFeature::RangeWidened => FixTemplateId::Fix5,
        VerdictFeature::UncoveredRegion => FixTemplateId::Fix6,
        VerdictFeature::MutexOverlap => FixTemplateId::Fix7,
        VerdictFeature::DenominatorZero => FixTemplateId::Fix8,
        VerdictFeature::BoundaryValue => FixTemplateId::Fix9,
        VerdictFeature::Timeout => FixTemplateId::Fix10,
        VerdictFeature::UnknownRiskLogic => FixTemplateId::Fix11,
        VerdictFeature::EmptyCore => FixTemplateId::Fix12,
        VerdictFeature::NonlinearConstruct => FixTemplateId::Fix13,
        VerdictFeature::GroundingBudgetExceeded => FixTemplateId::Fix14,
        VerdictFeature::SolverUnavailable => FixTemplateId::Fix15,
        VerdictFeature::CrossvalMismatch => FixTemplateId::Fix16,
    }
}

/// 便利函数：从反例中取首个越界字段的 `(字段, 当前值)`。
pub fn first_field_of(ce: &Counterexample, field: &str) -> Option<String> {
    ce.entity_snapshots
        .iter()
        .find_map(|e| e.fields.iter().find(|f| f.name == field))
        .map(|f| f.value.clone())
}

/// 取反例中某字段的整数值（供区间化与诊断）。
pub fn int_field_of(ce: &Counterexample, field: &str) -> Option<i128> {
    ce.entity_snapshots
        .iter()
        .find_map(|e| e.fields.iter().find(|f| f.name == field))
        .and_then(|f| f.value.parse::<i128>().ok())
}

/// 便利：从赋值中取某符号的整数值。
pub fn int_of(assignment: &Assignment, symbol: &str) -> Option<i128> {
    assignment.get(symbol).and_then(as_int)
}

/// 便利：从赋值中取某符号的位向量值。
pub fn bv_of(assignment: &Assignment, symbol: &str) -> Option<(u128, u32)> {
    assignment.get(symbol).and_then(as_bv)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Value;

    #[test]
    fn ipv4_formatting() {
        assert_eq!(format_ip(0x0A00_0100, 32), "10.0.1.0");
        assert_eq!(format_ip(0x0A00_0100, 32), "10.0.1.0");
    }

    #[test]
    fn enum_values_are_resolved_to_member_names() {
        let s = Sort::Enum(vec!["Basic".into(), "Enhanced".into()]);
        assert_eq!(format_value(&Value::Int(1), &s), "Enhanced");
        assert_eq!(format_value(&Value::Int(9), &s), "<out-of-range enum 9>");
    }

    #[test]
    fn fix_rendering_is_deterministic_and_substitutes() {
        let a = render_fix(
            FixTemplateId::Fix3,
            &[("entity", "Service"), ("field", "host_ip"), ("value", "10.0.2.9"), ("expected", "10.0.1.0/24")],
        );
        let b = render_fix(
            FixTemplateId::Fix3,
            &[("entity", "Service"), ("field", "host_ip"), ("value", "10.0.2.9"), ("expected", "10.0.1.0/24")],
        );
        assert_eq!(a, b);
        assert!(a.contains("10.0.1.0/24"));
        assert!(!a.contains("{"));
    }

    #[test]
    fn placeholder_cleanup_is_deterministic() {
        assert_eq!(cleanup_placeholders("a {x} b {y}"), "a n/a b n/a");
        assert_eq!(cleanup_placeholders("保留 {中文} 与 {}"), "保留 {中文} 与 {}");
        assert_eq!(cleanup_placeholders("{a}"), "n/a");
        assert_eq!(cleanup_placeholders("no braces"), "no braces");
    }

    #[test]
    fn every_feature_maps_to_a_template() {
        for f in [
            VerdictFeature::SameHostPortConflict,
            VerdictFeature::DbInstanceDivergence,
            VerdictFeature::OutOfSubnet,
            VerdictFeature::ConflictingBoundPair,
            VerdictFeature::RangeWidened,
            VerdictFeature::UncoveredRegion,
            VerdictFeature::MutexOverlap,
            VerdictFeature::DenominatorZero,
            VerdictFeature::BoundaryValue,
            VerdictFeature::Timeout,
            VerdictFeature::UnknownRiskLogic,
            VerdictFeature::EmptyCore,
            VerdictFeature::NonlinearConstruct,
            VerdictFeature::GroundingBudgetExceeded,
            VerdictFeature::SolverUnavailable,
            VerdictFeature::CrossvalMismatch,
        ] {
            assert!(!fix_template(template_for(f)).is_empty());
        }
    }

    #[test]
    fn core_attribution_sorts_by_line() {
        let s1 = Span::new(30, 5, 31, 48);
        let s2 = Span::new(10, 3, 11, 9);
        let labels = vec![
            ("A".to_string(), "RuleA".to_string(), s1),
            ("B".to_string(), "RuleB".to_string(), s2),
        ];
        let r = attribute_core(&["A".to_string(), "B".to_string()], &labels);
        assert_eq!(r[0].rule_name, "RuleB");
        assert_eq!(r[1].rule_name, "RuleA");
        assert_eq!(r[1].start_line, 30);
    }
}
