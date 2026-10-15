//! `policylang-check`（CR-3）— 符号表、类型检查、可判定性守卫、逻辑探针与展开预算。
//!
//! 对应文档：`02 §2.3`、`05 §4`–`§6`、`03 §3.3`（`W1`–`W12`）、`03 §3.4`（类型系统）、
//! `03 §3.9`（预算）、`06 §6.4.1`（足迹置位）。
//!
//! 入口为 [`check`]：`&Spec + &CheckOptions → Result<CheckedSpec, Vec<Diagnostic>>`。

pub mod budget;
pub mod guardian;
pub mod logic_profile;
pub mod symbol_table;
pub mod typecheck;

use std::collections::BTreeMap;

use policylang_ast::diag::Diagnostic;
use policylang_ast::spec::{LogicProfile, Spec};

pub use budget::{GroundMeasure, G_MAX_DEFAULT};
pub use guardian::{LabelKind, LabelMap};
pub use symbol_table::{DomainInfo, SymbolTable};

/// 检查选项（对应 CLI 开关；`01 §4 IF-1`）。
#[derive(Debug, Clone)]
pub struct CheckOptions {
    /// 展开预算 `G_max`（`W11`），默认 `10⁶`（`03 §3.9`）。
    pub max_groundings: u64,
    /// 是否放行非线性（`--allow-nonlinear`）。**`OQ-5` 建议删除该开关**；默认 `false`。
    pub allow_nonlinear: bool,
    /// `mutex` 目标的分支对数上限（`06 §6.3.6`），默认 64。
    pub mutex_max_pairs: usize,
    /// 单条正则的转译规模预算（`E-REGEX-BUDGET`），默认 4096。
    pub regex_budget: u64,
    /// `--strict-logic`：档位回落即报 `E-LOGIC-UNSUPPORTED`（`06 §6.4.2`）。
    pub strict_logic: bool,
}

impl Default for CheckOptions {
    fn default() -> Self {
        CheckOptions {
            max_groundings: G_MAX_DEFAULT as u64,
            allow_nonlinear: false,
            mutex_max_pairs: 64,
            regex_budget: 4096,
            strict_logic: false,
        }
    }
}

/// 通过检查的规范（`CheckedSpec`，`02 §1.3` 的 ② 产物）。
#[derive(Debug, Clone)]
pub struct CheckedSpec {
    pub spec: Spec,
    pub symbols: SymbolTable,
    /// 策略 → 规则合取的理论足迹。
    pub policy_profiles: BTreeMap<String, LogicProfile>,
    /// 不变量 → 足迹。
    pub invariant_profiles: BTreeMap<String, LogicProfile>,
    /// `require` → 足迹。
    pub require_profiles: BTreeMap<String, LogicProfile>,
    /// 目标 → 展开度量（`W11`）。
    pub groundings: BTreeMap<String, GroundMeasure>,
    /// `:named` 标签表（`NM-3`）。
    pub labels: LabelMap,
    /// 非阻断级诊断（告警）。
    pub warnings: Vec<Diagnostic>,
}

impl CheckedSpec {
    /// 某策略的档位候选名（`06 §6.4.2` 真值表）。
    pub fn logic_of_policy(&self, policy: &str) -> &'static str {
        self.policy_profiles
            .get(policy)
            .map(|p| p.candidate_logic())
            .unwrap_or("QF_UF")
    }
}

/// 执行全部检查。
///
/// 错误级诊断使整体返回 `Err`（`04 §11`：编译期错误 ⇒ 退出码 `3`）。
pub fn check(spec: &Spec, opts: &CheckOptions) -> Result<CheckedSpec, Vec<Diagnostic>> {
    let mut errors: Vec<Diagnostic> = Vec::new();
    let mut warnings: Vec<Diagnostic> = Vec::new();

    // ① 符号表（D-1 拓扑序 / 重复名 / 未知实体）
    let symbols = match SymbolTable::build(spec) {
        Ok(t) => t,
        Err(ds) => return Err(ds),
    };

    // ② 声明级类型与范围（W1–W4、@key）
    typecheck::check_declarations(spec, &symbols, &mut errors);

    // ③ 策略形状（W6 / W12 / mutex 预算）
    for p in &spec.policies {
        guardian::check_policy_shape(p, opts, &mut errors);
    }

    // ④ 逐公式：排序 + 作用域 + W8 + 足迹
    let mut policy_profiles: BTreeMap<String, LogicProfile> = BTreeMap::new();
    let mut invariant_profiles: BTreeMap<String, LogicProfile> = BTreeMap::new();
    let mut require_profiles: BTreeMap<String, LogicProfile> = BTreeMap::new();

    let collect = |forms: Vec<&policylang_ast::formula::Formula>,
                   label: &str,
                   errors: &mut Vec<Diagnostic>,
                   warnings: &mut Vec<Diagnostic>|
     -> LogicProfile {
        let mut ck = typecheck::FormulaChecker::new(&symbols, opts, spec);
        for f in forms {
            // 检查结果只用于副作用（诊断/足迹）；错误经下方 diags 统一收集。
            let _ = ck.check(f);
        }
        let (profile, diags) = ck.finish();
        for d in diags {
            if d.is_error() {
                errors.push(d);
            } else {
                warnings.push(d);
            }
        }
        if let Some(w) = logic_profile::fallback_warning(label, &profile) {
            warnings.push(w);
        }
        if opts.strict_logic && profile.candidate_logic() == "ALL" && !profile.nonlinear_opt_in {
            errors.push(Diagnostic::error(
                policylang_ast::codes::E_LOGIC_UNSUPPORTED,
                format!("`{label}` 在 `--strict-logic` 下发生档位回落（06 §6.4.2）"),
            ));
        }
        profile
    };

    for p in &spec.policies {
        let forms: Vec<&policylang_ast::formula::Formula> =
            p.rules.iter().map(|r| &r.formula).collect();
        let prof = collect(forms, &p.name, &mut errors, &mut warnings);
        policy_profiles.insert(p.name.clone(), prof);

        // 分支单独检查（其足迹并入 completeness 目标）
        let bforms: Vec<&policylang_ast::formula::Formula> =
            p.branches.iter().map(|b| &b.formula).collect();
        if !bforms.is_empty() {
            let bprof = collect(
                bforms,
                &format!("{}::branches", p.name),
                &mut errors,
                &mut warnings,
            );
            if let Some(entry) = policy_profiles.get_mut(&p.name) {
                entry.merge_from(&bprof);
            }
        }
    }
    for i in &spec.invariants {
        let prof = collect(
            vec![&i.formula],
            &i.name,
            &mut errors,
            &mut warnings,
        );
        invariant_profiles.insert(i.name.clone(), prof);
    }
    for r in &spec.requires {
        let prof = collect(
            vec![&r.formula],
            &r.name,
            &mut errors,
            &mut warnings,
        );
        require_profiles.insert(r.name.clone(), prof);
    }

    // ⑤ verify 引用与前置
    for v in &spec.verifies {
        guardian::check_verify(v, &symbols, &mut errors);
    }

    // ⑥ W11 展开预算
    let groundings = guardian::check_budget(spec, &symbols, opts, &mut errors);

    // ⑦ :named 标签唯一性
    let labels = match guardian::collect_labels(spec) {
        Ok(m) => m,
        Err(ds) => {
            errors.extend(ds);
            BTreeMap::new()
        }
    };

    if errors.iter().any(Diagnostic::is_error) {
        return Err(errors);
    }

    Ok(CheckedSpec {
        spec: spec.clone(),
        symbols,
        policy_profiles,
        invariant_profiles,
        require_profiles,
        groundings,
        labels,
        warnings,
    })
}

#[cfg(test)]
pub(crate) mod testutil {
    use policylang_ast::Spec;

    /// 解析一段 `.plm` 片段（自动补 `#lang` 头）。仅供本 crate 测试使用。
    pub fn spec_of(body: &str) -> Spec {
        let src = if body.trim_start().starts_with("#lang") {
            body.to_string()
        } else {
            format!("#lang policylang 2\n{body}")
        };
        policylang_parser::parse_spec(&src, None)
            .unwrap_or_else(|d| panic!("测试片段应可解析：{d:?}\n---\n{src}"))
    }
}
