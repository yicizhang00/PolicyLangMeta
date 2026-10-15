//! UNSAT 证明的**结构性校验**（`06 §6.7.2`，Alethe 格式）。
//!
//! ## 为什么值得做
//! `unsat` 只说明求解器**声称**不可满足。对高保证场景（合规、金融），一条可被独立
//! 检查的证明把「信任求解器」降级为「信任一个可复核的推导」。本模块做**结构级**校验
//! （非完备的证明检查器），能在不解码具体理论规则的前提下拦住三类常见问题：
//!
//! 1. **空结论不是 `false`**——Alethe 要求最后一步结论为空子句 `false`；
//! 2. **存在 `hole`**——Alethe 用 `hole` 表示「未证明的洞」，含 `hole` 的证明不可采信；
//! 3. **前提引用悬空**——`(step @p5 … :premises (@p9))` 引用了尚未定义的 `@p9`；
//! 4. **假设与查询无关**——若非 `assume` 的公式与查询中的断言**完全无交集**，
//!    说明拿到的不是本次查询的证明。
//!
//! ## 实测（本机 2026-10-15，cvc5 1.4.2）
//! ```text
//! unsat
//! (
//! (declare-const x Int)
//! (define @t1 () (* -1 11))
//! (assume @p1 (> x 10))
//! (assume @p2 (< x 5))
//! (step @p3 false :rule eq_resolve :premises (@p37 @p16))
//! )
//! ```
//! cvc5 默认即输出该形式；`z3` 的 `get-proof` 输出**不是** Alethe（为其私有格式），
//! 故本校验只对 Alethe 生效——非 Alethe 文本会被判为「不可校验」而非「校验失败」。
//!
//! **校验失败 ⇒ 不得采信该 `unsat`**：调用方应降级为 `UnknownReviewRequired` 并
//! 标注 `proof_checked = false`（与 `G-8` 诚实阻断一致）。

use policylang_diagnostics::sexpr::SExpr;

/// Alethe 允许的**顶层**步骤名。
///
/// 含 `assume-push`：cvc5 在增量/`push` 语境下用它代替 `assume`
/// （实测缺失会导致一份合法证明被误判为「非 Alethe」）。
/// 另含 `declare-var` / `declare-codatatype` 等 Alethe 规范中的前置声明形式。
const ALETHE_RULES: &[&str] = &[
    "assume",
    "assume-push",
    "step",
    "anchor",
    "define",
    "declare-const",
    "declare-fun",
    "declare-sort",
    "declare-var",
    "declare-datatype",
    "declare-codatatype",
    // 增量/`push`-`pop` 语境下的 Alethe 扩展（cvc5 实测会产出）
    "step-push",
    "step-pop",
    "hole",
];

/// 校验结论。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofCheck {
    /// 是否通过**结构级**校验。`false` 表示**不得**采信本次 `unsat`。
    pub checked: bool,
    /// 是否为 Alethe 格式（`false` 表示后端输出私有格式，无法校验 ⇒ `checked = false`）。
    pub is_alethe: bool,
    pub steps: usize,
    pub assumptions: usize,
    /// 是否含 `hole`（Alethe 的「未证明洞」）。
    pub has_hole: bool,
    /// 阻塞性问题（`checked = false` 的依据）。
    pub errors: Vec<String>,
    /// 非阻塞性说明（如某条 `assume` 未与断言文本精确匹配）。
    pub notes: Vec<String>,
}

impl ProofCheck {
    fn fail(is_alethe: bool, msg: impl Into<String>) -> Self {
        ProofCheck {
            checked: false,
            is_alethe,
            steps: 0,
            assumptions: 0,
            has_hole: false,
            errors: vec![msg.into()],
            notes: Vec::new(),
        }
    }

    /// 供报告与诊断使用的一行摘要。
    pub fn summary(&self) -> String {
        if self.checked {
            format!(
                "证明结构校验通过（{} 步，{} 条假设，Alethe）",
                self.steps, self.assumptions
            )
        } else if !self.is_alethe {
            "证明非 Alethe 格式，无法结构性校验".to_string()
        } else {
            format!("证明结构校验失败：{}", self.errors.join("；"))
        }
    }
}

/// 从 `get-proof` 的响应流中取出证明的 S-Expr 文本。
///
/// 取判定之后的**首个以 Alethe 步骤名开头**的列表，而不是「首个列表」——
/// 实测 cvc5 在证明之前可能先给出 `(error …)` 或其它响应，直接取首个列表会拿到
/// 错误对象，导致把一份合法 Alethe 证明误判为「非 Alethe 格式」（真实踩过的坑）。
pub fn extract_proof(stdout: &str) -> Option<String> {
    let mut seen_verdict = false;
    let mut fallback: Option<String> = None;
    for item in crate::response::top_level_items(stdout) {
        match &item {
            SExpr::Atom(a) if a == "unsat" => {
                seen_verdict = true;
                continue;
            }
            SExpr::List(v) if seen_verdict => {
                let head = v.first().and_then(SExpr::as_atom).unwrap_or("");
                if ALETHE_RULES.contains(&head) && head != "hole" {
                    return Some(item.to_text());
                }
                // 非证明对象（`error` / `model` / `objectives` …）：跳过并留作兜底
                if head != "error" && fallback.is_none() {
                    fallback = Some(item.to_text());
                }
            }
            _ => {}
        }
    }
    fallback
}

/// 去掉脚本中的**载荷命令**，得到可追加 `(get-proof)` 的干净前提。
///
/// 载荷：`check-sat` / `get-model` / `get-unsat-core` / `get-objectives` / `get-proof`。
pub fn strip_payload(script: &str) -> String {
    const STRIP: &[&str] = &[
        "(check-sat)",
        "(get-model)",
        "(get-unsat-core)",
        "(get-objectives)",
        "(get-proof)",
    ];
    let mut s = String::new();
    for line in script.lines() {
        let t = line.trim_start();
        if STRIP.iter().any(|c| t.starts_with(c)) {
            continue;
        }
        s.push_str(line);
        s.push('\n');
    }
    s
}

/// 由基础查询脚本构造「取证明」脚本（追加 `:produce-proofs` 与 `(get-proof)`）。
pub fn build_proof_script(base: &str) -> String {
    let s = strip_payload(base);
    // `:produce-proofs` 必须紧随其他 set-option（`CO-2`）
    let mut out = String::new();
    let mut inserted = false;
    for line in s.lines() {
        out.push_str(line);
        out.push('\n');
        if !inserted && line.trim_start().starts_with("(set-option") {
            out.push_str("(set-option :produce-proofs true)\n");
            inserted = true;
        }
    }
    if !inserted {
        out = format!("(set-option :produce-proofs true)\n{out}");
    }
    out.push_str("(check-sat)\n(get-proof)\n");
    out
}

/// 归一化 S-Expr 文本：折叠空白、去除空白差异。
fn norm(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut prev_space = false;
    for c in s.chars() {
        if c.is_whitespace() {
            if !prev_space {
                out.push(' ');
            }
            prev_space = true;
        } else {
            out.push(c);
            prev_space = false;
        }
    }
    out.trim().to_string()
}

/// 从查询脚本中抽取**被断言的公式**文本（剥掉 `(assert (! X :named Y))` 的包装）。
pub fn asserted_forms(script: &str) -> Vec<String> {
    let mut out = Vec::new();
    for item in crate::response::top_level_items(&strip_payload(script)) {
        let Some(v) = item.as_list() else { continue };
        if v.first().and_then(SExpr::as_atom) != Some("assert") {
            continue;
        }
        let Some(body) = v.get(1) else { continue };
        // `(assert (! X :named Y))` ⇒ 取 X
        if let Some(inner) = body.as_list() {
            if inner.first().and_then(SExpr::as_atom) == Some("!") {
                if let Some(x) = inner.get(1) {
                    out.push(norm(&x.to_text()));
                    continue;
                }
            }
        }
        out.push(norm(&body.to_text()));
    }
    out
}

/// 对 Alethe 证明做**结构级**校验。
pub fn check_alethe(proof_text: &str, assertions: &[String]) -> ProofCheck {
    let parsed = match policylang_diagnostics::parse_one(proof_text) {
        Ok(e) => e,
        Err(e) => return ProofCheck::fail(false, format!("证明无法解析为 S-Expr：{e}")),
    };
    let Some(steps) = parsed.as_list() else {
        return ProofCheck::fail(false, "证明顶层不是列表");
    };
    if steps.is_empty() {
        return ProofCheck::fail(true, "证明为空（无任何步骤）");
    }

    let mut res = ProofCheck {
        checked: false,
        is_alethe: true,
        steps: 0,
        assumptions: 0,
        has_hole: false,
        errors: Vec::new(),
        notes: Vec::new(),
    };

    // 已定义的步骤 id（用于检测悬空前提引用）
    let mut defined: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut last_conclusion: Option<String> = None;
    let asserted: std::collections::BTreeSet<String> = assertions.iter().cloned().collect();
    let mut matched_assumes = 0usize;

    for (i, st) in steps.iter().enumerate() {
        let Some(v) = st.as_list() else {
            res.errors.push(format!("第 {} 个顶层项不是列表", i + 1));
            continue;
        };
        let Some(head) = v.first().and_then(SExpr::as_atom) else {
            res.errors.push(format!("第 {} 个顶层项缺少规则名", i + 1));
            continue;
        };
        if !ALETHE_RULES.contains(&head) {
            // 首个非 Alethe 规则名 ⇒ 判为「非 Alethe 格式」，而非「校验失败」
            res.is_alethe = false;
            res.errors
                .push(format!("出现非 Alethe 规则名 `{head}`（第 {} 项）", i + 1));
            res.checked = false;
            return res;
        }

        match head {
            "assume" | "assume-push" => {
                res.assumptions += 1;
                let id = v.get(1).and_then(SExpr::as_atom).unwrap_or("");
                if !id.is_empty() {
                    defined.insert(id.to_string());
                }
                if let Some(f) = v.get(2) {
                    let n = norm(&f.to_text());
                    if asserted.contains(&n) {
                        matched_assumes += 1;
                    } else {
                        res.notes.push(format!("`assume {id}` 的公式未与断言精确匹配：{n}"));
                    }
                }
            }
            "hole" => {
                res.has_hole = true;
            }
            "step" | "step-push" | "step-pop" => {
                res.steps += 1;
                let id = v.get(1).and_then(SExpr::as_atom).unwrap_or("");
                if id.is_empty() {
                    res.errors.push(format!("第 {} 个 step 缺少 id", i + 1));
                }
                let conclusion = v.get(2).map(|x| norm(&x.to_text()));
                if let Some(c) = &conclusion {
                    last_conclusion = Some(c.clone());
                }
                // 检查 `:premises` 引用是否已定义
                let mut k = 3usize;
                while k < v.len() {
                    if let Some(kw) = v[k].as_atom() {
                        if kw == ":premises" {
                            if let Some(lst) = v.get(k + 1).and_then(|x| x.as_list()) {
                                for p in lst {
                                    if let Some(pid) = p.as_atom() {
                                        if !defined.contains(pid) {
                                            res.errors.push(format!(
                                                "step `{id}` 引用了未定义的前提 `{pid}`（第 {} 项，应在之前定义）",
                                                i + 1
                                            ));
                                        }
                                    }
                                }
                            }
                            k += 2;
                            continue;
                        }
                    }
                    k += 1;
                }
                if !id.is_empty() {
                    defined.insert(id.to_string());
                }
            }
            // 前置声明：登记 id 以便后续引用
            _ => {
                if let Some(id) = v.get(1).and_then(SExpr::as_atom) {
                    defined.insert(id.to_string());
                }
            }
        }
    }

    // ① 不得含 hole
    if res.has_hole {
        res.errors
            .push("证明含 `hole`（Alethe 的未证明洞）⇒ 不可采信".to_string());
    }
    // ② 末步结论必须为 `false`
    match &last_conclusion {
        Some(c) if c == "false" => {}
        Some(c) => res
            .errors
            .push(format!("末步结论为 `{c}`，而 Alethe 要求空子句 `false`")),
        None => res.errors.push("证明中不含任何 `step`".to_string()),
    }
    // ③ 假设必须与本次查询有关（全无交集 ⇒ 拿到的是别的查询的证明）
    if res.assumptions > 0 && matched_assumes == 0 {
        res.errors
            .push("证明的全部 `assume` 均未与本次查询的断言匹配 ⇒ 该证明与本次验证无关".to_string());
    }

    res.checked = res.errors.is_empty();
    res
}

#[cfg(test)]
mod tests {
    use super::*;

    const WELL_FORMED: &str = "(
(declare-const x Int)
(define @t1 () (* -1 11))
(assume @p1 (> x 10))
(assume @p2 (< x 5))
(step @p3 (@t1 @t1) :rule eq_reflexive)
(step @p4 false :rule eq_resolve :premises (@p3 @p1))
)";

    fn assert_list() -> Vec<String> {
        vec!["(> x 10)".to_string(), "(< x 5)".to_string()]
    }

    #[test]
    fn well_formed_proof_passes() {
        let r = check_alethe(WELL_FORMED, &assert_list());
        assert!(r.checked, "{:?}", r);
        assert!(r.is_alethe);
        assert_eq!(r.steps, 2);
        assert_eq!(r.assumptions, 2);
        assert!(!r.has_hole);
    }

    #[test]
    fn assume_push_is_recognized_as_alethe() {
        // 回归：cvc5 在增量语境下用 `assume-push`，遗漏该名会把合法证明误判为非 Alethe
        let p = WELL_FORMED.replace("(assume @p1 (> x 10))", "(assume-push @p1 (> x 10))");
        let r = check_alethe(&p, &assert_list());
        assert!(r.is_alethe, "{:?}", r.errors);
        assert!(r.checked, "{:?}", r.errors);
    }

    #[test]
    fn hole_makes_proof_untrustworthy() {
        let p = WELL_FORMED.replace(
            "(step @p4 false :rule eq_resolve :premises (@p3 @p1))",
            "(hole @p4 false)\n(step @p5 false :rule eq_resolve :premises (@p3 @p1))",
        );
        let r = check_alethe(&p, &assert_list());
        assert!(!r.checked);
        assert!(r.has_hole);
        assert!(r.errors.iter().any(|e| e.contains("hole")), "{:?}", r.errors);
    }

    #[test]
    fn last_conclusion_must_be_false() {
        let p = WELL_FORMED.replace(
            "(step @p4 false :rule eq_resolve :premises (@p3 @p1))",
            "(step @p4 (>= x 11) :rule eq_resolve :premises (@p3 @p1))",
        );
        let r = check_alethe(&p, &assert_list());
        assert!(!r.checked);
        assert!(r.errors.iter().any(|e| e.contains("false")), "{:?}", r.errors);
    }

    #[test]
    fn dangling_premise_is_rejected() {
        let p = WELL_FORMED.replace("(@p3 @p1)", "(@p3 @p99)");
        let r = check_alethe(&p, &assert_list());
        assert!(!r.checked);
        assert!(r.errors.iter().any(|e| e.contains("@p99")), "{:?}", r.errors);
    }

    #[test]
    fn foreign_assumptions_are_rejected() {
        let p = WELL_FORMED.replace("(> x 10)", "(> y 42)").replace("(< x 5)", "(< y 0)");
        let r = check_alethe(&p, &assert_list());
        assert!(!r.checked);
        assert!(
            r.errors.iter().any(|e| e.contains("与本次验证无关")),
            "{:?}",
            r.errors
        );
    }

    #[test]
    fn denormalized_whitespace_still_matches() {
        // 证明里的公式换行/多空格不应导致误判为「无关」
        let p = WELL_FORMED.replace("(assume @p1 (> x 10))", "(assume @p1 (>  x\n 10))");
        let r = check_alethe(&p, &assert_list());
        assert!(r.checked, "{:?}", r);
    }

    #[test]
    fn non_alethe_is_reported_as_uncheckable_not_failed() {
        // z3 的私有证明格式：应判 is_alethe=false（不可校验），而不是「校验失败」
        let p = "(proof\n(let (($x41 (>= x 0))) (th_lemma $x41))\n)";
        let r = check_alethe(p, &assert_list());
        assert!(!r.checked);
        assert!(!r.is_alethe);
        assert!(r.summary().contains("非 Alethe"));
    }

    #[test]
    fn extract_proof_takes_first_list_after_verdict() {
        let out = "unsat\n(\n(assume @p1 (> x 10))\n(step @p2 false :rule x)\n)\n";
        let p = extract_proof(out).expect("应能取出证明");
        assert!(p.starts_with('('), "{p}");
        assert!(p.contains("assume @p1"));
        // 未判定时不应误取
        assert_eq!(extract_proof("sat\n(model)\n"), None);
    }

    #[test]
    fn extract_proof_skips_leading_error_response() {
        // 回归：cvc5 可能在证明前先输出 `(error …)`；直接取「首个列表」会把错误对象
        // 当作证明，进而误判为「非 Alethe 格式」。
        let out = "unsat\n(error \"some warning\")\n(assume @p1 (> x 10))\n(step @p2 false :rule x)\n";
        let p = extract_proof(out).expect("应跳过 error 取到证明");
        assert!(p.contains("assume @p1"), "{p}");
    }

    #[test]
    fn build_proof_script_appends_options_and_query() {
        let base = "; h\n(set-logic QF_LIA)\n(set-option :produce-models true)\n\
                    (declare-fun x () Int)\n(assert (> x 1))\n(check-sat)\n(get-model)\n";
        let s = build_proof_script(base);
        assert!(s.contains("(set-option :produce-proofs true)"));
        assert!(s.contains("(get-proof)"));
        assert_eq!(s.matches("(check-sat)").count(), 1);
        assert!(!s.contains("(get-model)"));
        // `:produce-proofs` 必须在 `(check-sat)` 之前
        assert!(s.find(":produce-proofs").unwrap() < s.find("(check-sat)").unwrap());
    }

    #[test]
    fn asserted_forms_unwraps_named_assertions() {
        let base = "(assert (! (> x 10) :named A))\n(assert (>= y 0))\n(check-sat)\n";
        let f = asserted_forms(base);
        assert_eq!(f, vec!["(> x 10)".to_string(), "(>= y 0)".to_string()]);
    }
}
