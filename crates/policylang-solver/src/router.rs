//! 理论感知路由（`FR-8`、`06 §6.4.2`–`§6.4.5`，修正 `B-7`/`A-14`）。
//!
//! 路由**只依据 `ALG-3` 实测能力**，不依赖任何硬编码的逻辑名支持表。
//! 当精确档位无后端支持时按回落链降级：`<候选档位>` → `ALL`，并记 `W-LOGIC-FALLBACK`。

use policylang_ast::codes::{E_LOGIC_UNSUPPORTED, W_LOGIC_FALLBACK, W_SINGLE_BACKEND};
use policylang_ast::diag::Diagnostic;

use crate::orchestra::Backend;
use crate::probe::Capability;

/// 路由结果。
#[derive(Debug, Clone)]
pub struct Route {
    /// 实际将要发射的档位（可能因回落而变为 `ALL`）。
    pub logic: String,
    /// 初始候选档位（来自 `LogicProfile`）。
    pub candidate_logic: String,
    pub backends: Vec<Backend>,
    /// 是否发生了档位回落。
    pub fallback: bool,
    /// 被排除的后端及原因（审计用）。
    pub excluded: Vec<(String, String)>,
    pub diagnostics: Vec<Diagnostic>,
}

impl Route {
    pub fn is_empty(&self) -> bool {
        self.backends.is_empty()
    }
}

/// 路由选项。
#[derive(Debug, Clone)]
pub struct RouteOptions {
    /// `--strict-logic`：回落即报 `E-LOGIC-UNSUPPORTED`（exit 4）。
    pub strict_logic: bool,
    /// 用户显式指定的后端名集合（空 = 全部可用）。
    pub only: Vec<String>,
    /// 用户显式排除的后端名集合。
    pub exclude: Vec<String>,
}

impl Default for RouteOptions {
    fn default() -> Self {
        RouteOptions {
            strict_logic: false,
            only: Vec::new(),
            exclude: Vec::new(),
        }
    }
}

/// 依据实测能力选择后端集合。
pub fn route(candidate_logic: &str, caps: &[Capability], opts: &RouteOptions) -> Route {
    let mut diagnostics = Vec::new();
    let mut excluded: Vec<(String, String)> = Vec::new();

    let usable: Vec<&Capability> = caps
        .iter()
        .filter(|c| {
            if !c.available {
                excluded.push((c.name.clone(), "不可用（探测失败）".into()));
                return false;
            }
            if !opts.only.is_empty() && !opts.only.iter().any(|n| n == &c.name) {
                excluded.push((c.name.clone(), "未被 --solvers 选中".into()));
                return false;
            }
            if opts.exclude.iter().any(|n| n == &c.name) {
                excluded.push((c.name.clone(), "被 --exclude-solver 排除".into()));
                return false;
            }
            true
        })
        .collect();

    // ① 精确档位
    let mut picked: Vec<Backend> = usable
        .iter()
        .filter(|c| c.supports(candidate_logic))
        .map(|c| Backend {
            name: c.name.clone(),
            path: c.path.clone(),
        })
        .collect();

    if !picked.is_empty() {
        if picked.len() == 1 {
            diagnostics.push(Diagnostic::warning(
                W_SINGLE_BACKEND,
                format!(
                    "档位 `{candidate_logic}` 仅有一个后端支持（`{}`）：\
                     无法进行 SAT 模型重放的交叉验证（06 §6.7）",
                    picked[0].name
                ),
            ));
        }
        // 审计：记录「可用但未选中」的原因，便于排查路由结果
        for c in &usable {
            if !picked.iter().any(|b| b.name == c.name) {
                excluded.push((c.name.clone(), format!("实测不支持档位 `{candidate_logic}`")));
            }
        }
        return Route {
            logic: candidate_logic.to_string(),
            candidate_logic: candidate_logic.to_string(),
            backends: picked,
            fallback: false,
            excluded,
            diagnostics,
        };
    }

    // ② 回落链：候选档位 → ALL
    if candidate_logic != "ALL" {
        let all_caps: Vec<Backend> = usable
            .iter()
            .filter(|c| c.supports("ALL"))
            .map(|c| Backend {
                name: c.name.clone(),
                path: c.path.clone(),
            })
            .collect();
        if !all_caps.is_empty() {
            diagnostics.push(Diagnostic::warning(
                W_LOGIC_FALLBACK,
                format!(
                    "档位 `{candidate_logic}` 无后端支持（实测）：回落 `ALL`（06 §6.4.2 回落链）"
                ),
            ));
            picked = all_caps;
            if opts.strict_logic {
                diagnostics.push(Diagnostic::error(
                    E_LOGIC_UNSUPPORTED,
                    format!("`--strict-logic` 下不允许档次回落（`{candidate_logic}` → `ALL`）"),
                ));
            }
            return Route {
                logic: "ALL".to_string(),
                candidate_logic: candidate_logic.to_string(),
                backends: picked,
                fallback: true,
                excluded,
                diagnostics,
            };
        }
    }

    // ③ 兜底：使用全部可用后端，但标注风险（TH-3a：探测失败即禁用 Pass）
    if !usable.is_empty() {
        diagnostics.push(Diagnostic::warning(
            W_LOGIC_FALLBACK,
            format!(
                "档位 `{candidate_logic}` 与 `ALL` 均未通过实测：将向全部可用后端尝试；\
                 任何 `unsat` 仅记为 `UnknownReviewRequired`（TH-3a 保守立场）"
            ),
        ));
        if opts.strict_logic {
            diagnostics.push(Diagnostic::error(
                E_LOGIC_UNSUPPORTED,
                "`--strict-logic`：无可确认的档位支持",
            ));
        }
        picked = usable
            .iter()
            .map(|c| Backend {
                name: c.name.clone(),
                path: c.path.clone(),
            })
            .collect();
    }

    Route {
        logic: candidate_logic.to_string(),
        candidate_logic: candidate_logic.to_string(),
        backends: picked,
        fallback: false,
        excluded,
        diagnostics,
    }
}

/// 基线能力矩阵（`06 §6.4.4` 的**参考值**，仅供 `policylang solvers` 的对照展示；
/// 实际路由**一律以实测为准**）。
pub const BASELINE_MATRIX: &[(&str, &[&str], &[&str])] = &[
    ("z3", &["QF_LIA", "QF_LRA", "QF_LIRA", "QF_BV", "QF_BVLIA", "QF_SLIA", "ALL"], &["QF_BVLRA", "QF_BVLIRA"]),
    ("cvc5", &["QF_LIA", "QF_LRA", "QF_LIRA", "QF_BV", "QF_SLIA", "ALL"], &["QF_BVLIA"]),
    ("bitwuzla", &["QF_BV", "ALL"], &[]),
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::probe::Capability;
    use std::collections::BTreeSet;

    fn cap(name: &str, logics: &[&str]) -> Capability {
        Capability {
            name: name.into(),
            path: name.into(),
            version: Some("test".into()),
            available: true,
            logics: logics.iter().map(|s| s.to_string()).collect::<BTreeSet<_>>(),
            f_model: true,
            f_unsat_core: true,
            f_incremental: false,
            f_div_mod: true,
            f_regex_inter: true,
            f_proof: false,
            f_optimize: false,
            notes: vec![],
        }
    }

    #[test]
    fn exact_logic_routes_to_supporting_backends_only() {
        let caps = vec![cap("z3", &["QF_LIA", "QF_SLIA", "ALL"]), cap("bitwuzla", &["QF_BV"])];
        let r = route("QF_SLIA", &caps, &RouteOptions::default());
        assert_eq!(r.logic, "QF_SLIA");
        assert_eq!(r.backends.len(), 1);
        assert_eq!(r.backends[0].name, "z3");
        assert!(!r.fallback);
        // bitwuzla 被排除且原因可审计
        assert!(r.excluded.iter().any(|(n, _)| n == "bitwuzla"));
        // 单后端告警
        assert!(r.diagnostics.iter().any(|d| d.code == W_SINGLE_BACKEND));
    }

    #[test]
    fn unsupported_logic_falls_back_to_all() {
        let caps = vec![cap("z3", &["ALL"])];
        let r = route("QF_BVLIA", &caps, &RouteOptions::default());
        assert!(r.fallback);
        assert_eq!(r.logic, "ALL");
        assert_eq!(r.candidate_logic, "QF_BVLIA");
        assert!(r.diagnostics.iter().any(|d| d.code == W_LOGIC_FALLBACK));
    }

    #[test]
    fn strict_logic_rejects_fallback() {
        let caps = vec![cap("z3", &["ALL"])];
        let r = route(
            "QF_BVLIA",
            &caps,
            &RouteOptions {
                strict_logic: true,
                ..Default::default()
            },
        );
        assert!(r.diagnostics.iter().any(|d| d.code == E_LOGIC_UNSUPPORTED));
    }

    #[test]
    fn no_backends_yields_empty_route() {
        let r = route("QF_LIA", &[], &RouteOptions::default());
        assert!(r.is_empty());
    }

    #[test]
    fn explicit_selection_and_exclusion() {
        let caps = vec![cap("z3", &["QF_LIA"]), cap("cvc5", &["QF_LIA"])];
        let r = route(
            "QF_LIA",
            &caps,
            &RouteOptions {
                only: vec![],
                exclude: vec!["cvc5".into()],
                strict_logic: false,
            },
        );
        assert_eq!(r.backends.len(), 1);
        assert_eq!(r.backends[0].name, "z3");
        assert!(r.excluded.iter().any(|(n, why)| n == "cvc5" && why.contains("排除")));
    }
}
