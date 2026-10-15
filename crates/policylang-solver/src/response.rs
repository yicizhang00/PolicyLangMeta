//! 求解器响应流解析（`06 §6.8`，**修正 `B-11`**）。
//!
//! ## 规则 `R-4`：**禁止** `stdout.starts_with("sat")`
//! 上游用前缀匹配提取判定，存在三重缺陷：① 多响应时**错位**；② 前缀匹配**过宽**
//! （`satisfiable-unknown` 之类）；③ 未处理 `success` / 前导空白 / CRLF / BOM。
//!
//! 本模块改为**按序扫描**：把输出切成顶层项（原子或配平列表，尊重 `"…"` 与 `|…|`），
//! 再按项**精确相等**分类，并保持**响应序号**（调用方按命令序取值）。

use policylang_diagnostics::sexpr::SExpr;
use policylang_diagnostics::{extract_assignments, parse_core, Assignment};

/// 求解器原始判定。
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Verdict {
    Sat,
    Unsat,
    Unknown,
    /// 编译期错误（不来自求解器）。
    None,
}

impl Verdict {
    pub fn as_str(self) -> &'static str {
        match self {
            Verdict::Sat => "sat",
            Verdict::Unsat => "unsat",
            Verdict::Unknown => "unknown",
            Verdict::None => "none",
        }
    }

    /// 是否为**确定**判定（`unknown` 不算）。
    pub fn is_determinate(self) -> bool {
        matches!(self, Verdict::Sat | Verdict::Unsat)
    }

    /// 从字符串还原（用于报告回读）。
    pub fn from_str_opt(s: &str) -> Option<Verdict> {
        match s {
            "sat" => Some(Verdict::Sat),
            "unsat" => Some(Verdict::Unsat),
            "unknown" => Some(Verdict::Unknown),
            "none" => Some(Verdict::None),
            _ => None,
        }
    }
}

/// 一个响应项。
#[derive(Debug, Clone, PartialEq)]
pub enum Response {
    Verdict(Verdict),
    Success,
    Unsupported,
    Model(Assignment),
    Core(Vec<String>),
    Error(String),
    /// 未识别的项（原文保留）。
    Raw(String),
}

/// 解析结果（保序）。
#[derive(Debug, Clone, Default)]
pub struct ParsedOutput {
    pub responses: Vec<Response>,
    /// 是否检测到协议异常（如响应个数与命令数不符）。
    pub protocol_notes: Vec<String>,
}

impl ParsedOutput {
    /// 首个判定（按响应序）。
    pub fn verdict(&self) -> Option<Verdict> {
        self.responses.iter().find_map(|r| match r {
            Response::Verdict(v) => Some(*v),
            _ => None,
        })
    }

    pub fn model(&self) -> Option<&Assignment> {
        self.responses.iter().find_map(|r| match r {
            Response::Model(a) => Some(a),
            _ => None,
        })
    }

    pub fn core(&self) -> Option<&Vec<String>> {
        self.responses.iter().find_map(|r| match r {
            Response::Core(c) => Some(c),
            _ => None,
        })
    }

    pub fn errors(&self) -> Vec<&str> {
        self.responses
            .iter()
            .filter_map(|r| match r {
                Response::Error(e) => Some(e.as_str()),
                _ => None,
            })
            .collect()
    }

    /// **未预期**的错误（`06 §6.8.3`）：排除「同发 `get-model` / `get-unsat-core`」必然产生的错配。
    ///
    /// 只有本方法返回非空时才是真正的协议故障（`E-SOLVER-PROTOCOL`，exit 4）。
    pub fn unexpected_errors(&self) -> Vec<&str> {
        self.errors()
            .into_iter()
            .filter(|e| !is_expected_mismatch(e))
            .collect()
    }

    /// 求解器是否报「不支持的逻辑」（用于 `ALG-3` 与档位回落判定）。
    pub fn is_unsupported_logic(&self) -> bool {
        self.errors().iter().any(|e| {
            let l = e.to_ascii_lowercase();
            l.contains("unsupported logic") || l.contains("unknown logic") || l.contains("logic")
        })
    }
}

/// 该错误消息是否为**预期错配**（`06 §6.8.3`）。
///
/// ## 为什么必然存在预期错配
/// 生成器对所有目标**同发** `(get-model)` 与 `(get-unsat-core)`（`06 §6.1.1` 的设计决策）：
/// SMT-LIB 脚本是**静态文本**，在求解之前无法知道结果是 `sat` 还是 `unsat`，而两种结果
/// 各自需要不同的 payload。于是每次查询中必然有一个命令拿到与之不匹配的结果，
/// 其 `(error …)` 属**协议预期**而非故障——必须忽略，否则会把**有效判定**误降级为
/// `E-SOLVER-PROTOCOL`（实测：真实 z3/cvc5 下 `unsat` 判定被整条丢弃）。
///
/// 覆盖面按**实测消息**制定（z3 5.3.0 / cvc5 1.4.2，本机 2026-10-15）：
///
/// | 情形 | z3 | cvc5 |
/// |---|---|---|
/// | `unsat` 后 `(get-model)` | `model is not available` | `cannot get model unless after a SAT or UNKNOWN response.` |
/// | `sat` 后 `(get-unsat-core)` | `unsat core is not available` | `cannot get unsat core unless in unsat mode.` |
pub fn is_expected_mismatch(msg: &str) -> bool {
    let m = msg.to_ascii_lowercase();
    const PATTERNS: &[&str] = &[
        "model is not available",
        "unsat core is not available",
        "no unsat core available",
        "cannot get model",
        "cannot get unsat core",
        "unless after a sat",
        "unless in unsat mode",
        "produce-models",
        "produce-unsat-cores",
    ];
    PATTERNS.iter().any(|p| m.contains(p))
}

/// 解析求解器 stdout。
pub fn parse_responses(stdout: &str) -> ParsedOutput {
    let mut out = ParsedOutput::default();
    // 去 BOM、统一行尾
    let cleaned = stdout.trim_start_matches('\u{feff}').replace("\r\n", "\n");
    for item in top_level_items(&cleaned) {
        match classify(&item) {
            Some(r) => out.responses.push(r),
            None => out.responses.push(Response::Raw(item.to_text())),
        }
    }
    out
}

fn classify(item: &SExpr) -> Option<Response> {
    match item {
        SExpr::Atom(a) => match a.as_str() {
            // 精确相等，而非前缀匹配（R-4）
            "sat" => Some(Response::Verdict(Verdict::Sat)),
            "unsat" => Some(Response::Verdict(Verdict::Unsat)),
            "unknown" => Some(Response::Verdict(Verdict::Unknown)),
            "success" => Some(Response::Success),
            "unsupported" => Some(Response::Unsupported),
            _ => None,
        },
        SExpr::Str(_) => None,
        SExpr::List(v) => {
            if let Some(head) = v.first().and_then(SExpr::as_atom) {
                match head {
                    "error" => {
                        let msg = v.get(1).map(SExpr::to_text).unwrap_or_default();
                        return Some(Response::Error(msg));
                    }
                    "model" | "define-fun" | "define-fun-rec" => {
                        let a = extract_assignments(std::slice::from_ref(item));
                        // 空模型（无 define-fun）也视为模型响应
                        return Some(Response::Model(a));
                    }
                    _ => {}
                }
            }
            // 形如 `( )` 或 `(LABEL …)`：Unsat Core
            let all_atoms = v.iter().all(|x| matches!(x, SExpr::Atom(_)));
            if all_atoms {
                let core = parse_core(std::slice::from_ref(item));
                // `()` 是合法空核（E-EMPTY-CARRIER 判定依据）
                return Some(Response::Core(core));
            }
            // 兜底：若含 define-fun 则按模型处理
            let a = extract_assignments(std::slice::from_ref(item));
            if !a.is_empty() {
                return Some(Response::Model(a));
            }
            None
        }
    }
}

/// 把文本切成**顶层项**（尊重 `"…"`、`|…|`、`;` 注释、括号配平）。
pub fn top_level_items(input: &str) -> Vec<SExpr> {
    let mut items = Vec::new();
    let chars: Vec<char> = input.chars().collect();
    let mut i = 0usize;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == ';' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        if c == '(' {
            let start = i;
            let mut depth = 0i32;
            let mut in_str = false;
            let mut in_bar = false;
            while i < chars.len() {
                let d = chars[i];
                if in_str {
                    if d == '"' {
                        // `""` 在字串内表示一个字面引号
                        if chars.get(i + 1) == Some(&'"') {
                            i += 2;
                            continue;
                        }
                        in_str = false;
                    }
                } else if in_bar {
                    if d == '|' {
                        in_bar = false;
                    }
                } else {
                    match d {
                        '"' => in_str = true,
                        '|' => in_bar = true,
                        ';' => {
                            while i < chars.len() && chars[i] != '\n' {
                                i += 1;
                            }
                            continue;
                        }
                        '(' => depth += 1,
                        ')' => {
                            depth -= 1;
                            if depth == 0 {
                                i += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                }
                i += 1;
            }
            let text: String = chars[start..i.min(chars.len())].iter().collect();
            match policylang_diagnostics::parse_one(&text) {
                Ok(e) => items.push(e),
                Err(_) => items.push(SExpr::Atom(text)),
            }
            continue;
        }
        if c == '"' {
            let start = i;
            i += 1;
            while i < chars.len() {
                if chars[i] == '"' {
                    if chars.get(i + 1) == Some(&'"') {
                        i += 2;
                        continue;
                    }
                    i += 1;
                    break;
                }
                i += 1;
            }
            let text: String = chars[start..i.min(chars.len())].iter().collect();
            match policylang_diagnostics::parse_one(&text) {
                Ok(e) => items.push(e),
                Err(_) => items.push(SExpr::Atom(text)),
            }
            continue;
        }
        let start = i;
        while i < chars.len()
            && !chars[i].is_whitespace()
            && chars[i] != '('
            && chars[i] != ')'
        {
            i += 1;
        }
        items.push(SExpr::Atom(chars[start..i].iter().collect()));
    }
    items
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_single_verdict_precisely() {
        assert_eq!(parse_responses("sat\n").verdict(), Some(Verdict::Sat));
        assert_eq!(parse_responses("unsat").verdict(), Some(Verdict::Unsat));
        assert_eq!(parse_responses("unknown\n").verdict(), Some(Verdict::Unknown));
    }

    #[test]
    fn does_not_prefix_match() {
        // R-4 反例：上游 `starts_with("sat")` 会把下列内容误判为 sat
        let p = parse_responses("satisfiable-unknown\n");
        assert_eq!(p.verdict(), None);
        let p2 = parse_responses("(error \"sat-ish\")\n");
        assert_eq!(p2.verdict(), None);
    }

    #[test]
    fn handles_leading_blank_crlf_and_bom() {
        let p = parse_responses("\u{feff}\r\n  \r\nsat\r\n(model)\r\n");
        assert_eq!(p.verdict(), Some(Verdict::Sat));
    }

    #[test]
    fn multi_response_keeps_order() {
        let p = parse_responses("sat\n(model (define-fun x () Int 5))\n");
        assert_eq!(p.verdict(), Some(Verdict::Sat));
        assert_eq!(p.model().and_then(|m| policylang_diagnostics::int_of(m, "x")), Some(5));
    }

    #[test]
    fn parses_model_and_core() {
        let p = parse_responses("unsat\n(PLR__P__A PLR__P__B)\n");
        assert_eq!(p.verdict(), Some(Verdict::Unsat));
        assert_eq!(
            p.core().cloned().unwrap_or_default(),
            vec!["PLR__P__A".to_string(), "PLR__P__B".to_string()]
        );
    }

    #[test]
    fn empty_core_is_recognized() {
        let p = parse_responses("unsat\n()\n");
        assert!(p.core().map(|c| c.is_empty()).unwrap_or(false));
    }

    #[test]
    fn errors_are_captured_not_fatal() {
        // B-12：盲目同发 get-model / get-unsat-core 会产生预期错配
        let p = parse_responses("unsat\n(error \"model is not available\")\n(A B)\n");
        assert_eq!(p.verdict(), Some(Verdict::Unsat));
        assert_eq!(p.core().unwrap().len(), 2);
        assert_eq!(p.errors().len(), 1);
    }

    #[test]
    fn success_and_unsupported() {
        let p = parse_responses("success\nunsupported\nsat\n");
        assert!(matches!(p.responses[0], Response::Success));
        assert!(matches!(p.responses[1], Response::Unsupported));
        assert_eq!(p.verdict(), Some(Verdict::Sat));
    }

    #[test]
    fn unsupported_logic_is_detected() {
        let p = parse_responses("(error \"unsupported logic QF_BVLIA\")\n");
        assert!(p.is_unsupported_logic());
    }

    #[test]
    fn expected_mismatches_are_not_protocol_errors() {
        // 实测消息（本机 z3 5.3.0 / cvc5 1.4.2）
        for m in [
            "model is not available",
            "line 8 column 15: unsat core is not available",
            "cannot get model unless after a SAT or UNKNOWN response.",
            "cannot get unsat core unless in unsat mode.",
        ] {
            assert!(is_expected_mismatch(m), "应判为预期错配：{m}");
        }
        // 真故障不得被豁免
        assert!(!is_expected_mismatch(
            "invalid function application, arguments missing"
        ));
        assert!(!is_expected_mismatch("unsupported logic QF_BVLIA"));

        // 关键回归：`unsat` + 预期错配**不得**被升级为协议故障，
        // 否则真实求解器下的有效判定会被整条丢弃（曾经的真实缺陷）。
        let p = parse_responses("unsat\n(error \"model is not available\")\n(A B)\n");
        assert_eq!(p.verdict(), Some(Verdict::Unsat));
        assert!(p.unexpected_errors().is_empty());
        assert_eq!(p.errors().len(), 1, "预期错配仍应被记录以供审计");

        let p2 = parse_responses("sat\n(error \"invalid function application\")\n");
        assert_eq!(p2.unexpected_errors().len(), 1, "真故障必须被识别");
    }
}
