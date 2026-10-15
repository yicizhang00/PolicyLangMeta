//! 反例区间化（`06 §6.3.7`）。
//!
//! ## 为什么需要
//! 对含连续排序（`Int` / `Real`）字段的反例，求解器只返回**一个**模型点（通常恰是边界值）。
//! 若报告只呈现该点，读者会误以为「只有 `port = 80` 一处违规」，而实际整个
//! `port ∈ [80, 1023]` 都违规。规范因此要求给出该字段在**保持违规成立**前提下的
//! 可自由变动区间（`AC-3` 的 `[80,1023]` 即由本机制给出）。
//!
//! ## 实现方式（经真实求解器实测确定）
//! 用求解器的 **Optimize 扩展**：固定其余符号为已知模型值，对目标字段同时
//! `(minimize)` 与 `(maximize)`，并在 **`box` 优先级**下让二者在同一轮求解中一起优化
//! ⇒ **每个字段恰好 1 次查询**（契合规范「每个 1 次查询」）。
//!
//! 实测（本机 2026-10-15）：
//!
//! | 后端 | `:opt.priority box` + `minimize`/`maximize` | 结果 |
//! |---|---|---|
//! | z3 5.3.0 | 支持 | `(objectives (x 80) (x 1023))` ⇒ `[80, 1023]` |
//! | cvc5 1.4.2 | **不支持** | `Parse Error … got \`minimize\`` |
//! | bitwuzla 0.9.1 | 不支持 | — |
//!
//! 因此区间化**按后端能力启用**（`f_optimize`，由 `ALG-3` 实测），不可用时
//! 优雅降级为单点呈现（`range = null`），并**不**影响判定本身（`G-4` / `G-8`）。

use policylang_diagnostics::sexpr::SExpr;

/// 区间化后需要从基础脚本中**移除**的命令（否则会污染 `get-objectives` 的响应流）。
const STRIPPED: &[&str] = &["(check-sat)", "(get-model)", "(get-unsat-core)"];

/// 由基础反证脚本构造「反例邻域探测」脚本。
///
/// * `base`：原始查询脚本（含 `check-sat` / `get-model` / `get-unsat-core`）；
/// * `fixes`：`(SMT 符号, SMT 字面量)`——把其余符号**固定**到已得模型值，
///   从而把目标字段之外的自由度全部消去；
/// * `target`：待求区间的字段符号。
///
/// 输出脚本：`set-logic` → `set-options`（追加 `:opt.priority box`）→ 声明 → 边界 →
/// 固定断言 → `(minimize target)` / `(maximize target)` → `(check-sat)` → `(get-objectives)`。
pub fn build_interval_script(base: &str, fixes: &[(String, String)], target: &str) -> String {
    let mut s = String::new();
    let mut inserted = false;

    for line in base.lines() {
        let t = line.trim_start();
        if STRIPPED.iter().any(|c| t.starts_with(c)) {
            continue;
        }
        s.push_str(line);
        s.push('\n');
        // `:opt.priority` 必须在 `(minimize)` 之前；紧随最后一条 `set-option` 落位最稳。
        if !inserted && t.starts_with("(set-option") {
            s.push_str("(set-option :opt.priority box)\n");
            inserted = true;
        }
    }
    if !inserted {
        s = format!("(set-option :opt.priority box)\n{s}");
    }

    for (sym, lit) in fixes {
        s.push_str(&format!("(assert (= {sym} {lit}))\n"));
    }
    s.push_str(&format!("(minimize {target})\n"));
    s.push_str(&format!("(maximize {target})\n"));
    s.push_str("(check-sat)\n");
    s.push_str("(get-objectives)\n");
    s
}

/// 从 `(get-objectives)` 的响应流中取出 `target` 的 `(下界, 上界)`。
///
/// 依赖求解器**按 `minimize`/`maximize` 的声明顺序**输出条目（z3 实测如此）；
/// 若仅有一条（求解器只回一个目标）则退化为 `(v, v)`。
pub fn interval_from_objectives(stdout: &str, target: &str) -> Option<(String, String)> {
    let mut vals: Vec<String> = Vec::new();
    for item in crate::response::top_level_items(stdout) {
        let Some(v) = item.as_list() else { continue };
        if v.first().and_then(SExpr::as_atom) != Some("objectives") {
            continue;
        }
        for e in &v[1..] {
            let Some(pair) = e.as_list() else { continue };
            if pair.len() != 2 {
                continue;
            }
            if pair[0].as_atom() != Some(target) {
                continue;
            }
            vals.push(pair[1].to_text());
        }
    }
    match vals.len() {
        0 => None,
        1 => Some((vals[0].clone(), vals[0].clone())),
        _ => Some((vals[0].clone(), vals[1].clone())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const BASE: &str = "; header\n(set-logic QF_LIA)\n(set-option :produce-models true)\n\
                        (declare-fun PL_g_port () Int)\n(declare-fun PL_g_host () Int)\n\
                        (assert (<= 80 PL_g_port))\n\
                        (assert (! (> PL_g_port 1023) :named PLR__P))\n\
                        (check-sat)\n(get-model)\n(get-unsat-core)\n";

    #[test]
    fn interval_script_strips_payload_and_appends_objectives() {
        let s = build_interval_script(BASE, &[("PL_g_host".into(), "7".into())], "PL_g_port");
        // 载荷命令必须被移除（否则响应流里混入 model/core）
        assert!(!s.contains("(check-sat)\n(get-model)"));
        assert!(!s.contains("(get-unsat-core)"));
        assert_eq!(s.matches("(check-sat)").count(), 1, "{s}");
        // 固定断言 + 双向目标
        assert!(s.contains("(assert (= PL_g_host 7))"), "{s}");
        assert!(s.contains("(minimize PL_g_port)"), "{s}");
        assert!(s.contains("(maximize PL_g_port)"), "{s}");
        assert!(s.contains("(get-objectives)"), "{s}");
        // `:opt.priority box` 必须在 `(minimize)` 之前
        let p = s.find(":opt.priority box").expect("应设置 box 优先级");
        let m = s.find("(minimize").expect("应有 minimize");
        assert!(p < m, "`:opt.priority` 必须早于 `minimize`");
        // 原始断言（含 :named）保留，故「违规成立」的前提不变
        assert!(s.contains(":named PLR__P"), "{s}");
    }

    #[test]
    fn parses_z3_objectives_output() {
        // z3 5.3.0 实测输出
        let out = "sat\n(objectives\n (x 80)\n (x 1023)\n)\n";
        assert_eq!(
            interval_from_objectives(out, "x"),
            Some(("80".to_string(), "1023".to_string()))
        );
    }

    #[test]
    fn missing_or_single_objective_is_handled() {
        assert_eq!(interval_from_objectives("sat\n", "x"), None);
        assert_eq!(
            interval_from_objectives("sat\n(objectives (x 5))\n", "x"),
            Some(("5".to_string(), "5".to_string()))
        );
        // 目标名不匹配 ⇒ 不算命中
        assert_eq!(
            interval_from_objectives("sat\n(objectives (y 5) (y 9))\n", "x"),
            None
        );
    }

    #[test]
    fn negative_and_real_bounds_are_carried_verbatim() {
        let out = "sat\n(objectives\n (r (- 1.5))\n (r (/ 7 2))\n)\n";
        assert_eq!(
            interval_from_objectives(out, "r"),
            Some(("(- 1.5)".to_string(), "(/ 7 2)".to_string()))
        );
    }

    #[test]
    fn script_without_set_option_still_gets_priority() {
        let base = "(set-logic QF_LIA)\n(declare-fun x () Int)\n(check-sat)\n";
        let s = build_interval_script(base, &[], "x");
        assert!(s.starts_with("(set-option :opt.priority box)"), "{s}");
    }
}
