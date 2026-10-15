//! `ALG-3` 后端能力探测（`FR-17`、`06 §6.4.3`，修正 `A-14`）。
//!
//! 把逻辑名从「硬编码」降级为**候选名**：实际支持度由**运行期实测**决定。
//! 未探测成功的能力一律保守为 `false`（探测失败即禁用该档位的 `Pass` 输出，`TH-3a`）。

use std::collections::BTreeSet;
use std::time::Duration;

use crate::orchestra::{run_captured, run_captured_argv, Backend, ProcResult};
use crate::response::{parse_responses, Verdict};

/// 一个后端的能力画像。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Capability {
    pub name: String,
    pub path: String,
    pub version: Option<String>,
    pub available: bool,
    /// 实测通过的逻辑档位（`set-logic` 冒烟通过者）。
    pub logics: BTreeSet<String>,
    pub f_model: bool,
    pub f_unsat_core: bool,
    pub f_incremental: bool,
    pub f_div_mod: bool,
    pub f_regex_inter: bool,
    pub f_proof: bool,
    /// 是否支持 **Optimize 扩展**（`(minimize)`/`(maximize)` + `:opt.priority box`）。
    /// 供反例区间化使用（`06 §6.3.7`）；不支持时区间化优雅降级。
    pub f_optimize: bool,
    /// 探测中的失败说明（供诊断）。
    pub notes: Vec<String>,
}

impl Capability {
    pub fn unavailable(name: &str, path: &str, why: &str) -> Self {
        Capability {
            name: name.to_string(),
            path: path.to_string(),
            version: None,
            available: false,
            logics: BTreeSet::new(),
            f_model: false,
            f_unsat_core: false,
            f_incremental: false,
            f_div_mod: false,
            f_regex_inter: false,
            f_proof: false,
            f_optimize: false,
            notes: vec![why.to_string()],
        }
    }

    pub fn supports(&self, logic: &str) -> bool {
        self.available && self.logics.contains(logic)
    }
}

/// 默认待探测逻辑档位（`06 §6.4.2` 的全部可达档位）。
pub const CANDIDATE_LOGICS: &[&str] = &[
    "QF_UF",
    "QF_LIA",
    "QF_LRA",
    "QF_LIRA",
    "QF_BV",
    "QF_BVLIA",
    "QF_BVLRA",
    "QF_BVLIRA",
    "QF_SLIA",
];

/// `P4`：探测结果落盘（由调用方决定路径；本函数仅产生内容）。
pub fn capability_json(caps: &[Capability]) -> String {
    let mut s = String::from("{\n  \"probed_at\": null,\n  \"backends\": [\n");
    for (i, c) in caps.iter().enumerate() {
        s.push_str("    {\n");
        s.push_str(&format!("      \"name\": {},\n", json_str(&c.name)));
        s.push_str(&format!("      \"path\": {},\n", json_str(&c.path)));
        s.push_str(&format!(
            "      \"version\": {},\n",
            c.version
                .as_deref()
                .map(json_str)
                .unwrap_or_else(|| "null".into())
        ));
        s.push_str(&format!("      \"available\": {},\n", c.available));
        let logics: Vec<String> = c.logics.iter().map(|x| json_str(x)).collect();
        s.push_str(&format!("      \"logics\": [{}],\n", logics.join(", ")));
        s.push_str(&format!("      \"f_model\": {},\n", c.f_model));
        s.push_str(&format!("      \"f_unsat_core\": {},\n", c.f_unsat_core));
        s.push_str(&format!("      \"f_incremental\": {},\n", c.f_incremental));
        s.push_str(&format!("      \"f_div_mod\": {},\n", c.f_div_mod));
        s.push_str(&format!("      \"f_regex_inter\": {},\n", c.f_regex_inter));
        s.push_str(&format!("      \"f_proof\": {},\n", c.f_proof));
        s.push_str(&format!("      \"f_optimize\": {}\n", c.f_optimize));
        s.push_str(if i + 1 == caps.len() { "    }\n" } else { "    },\n" });
    }
    s.push_str("  ]\n}\n");
    s
}

fn json_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// 探测单个后端。
pub fn probe_backend(b: &Backend, timeout: Duration) -> Capability {
    let mut cap = Capability {
        name: b.name.clone(),
        path: b.path.clone(),
        version: None,
        available: false,
        logics: BTreeSet::new(),
        f_model: false,
        f_unsat_core: false,
        f_incremental: false,
        f_div_mod: false,
        f_regex_inter: false,
        f_proof: false,
        f_optimize: false,
        notes: Vec::new(),
    };

    // P1：`--version`
    let v = run_captured(&b.path, &["--version"], None, timeout);
    if let Some(e) = &v.spawn_error {
        cap.notes
            .push(format!("进程启动失败：{e}（E-SOLVER-MISSING 情形）"));
        return cap;
    }
    let version_text = format!("{}{}", v.stdout, v.stderr);
    cap.version = version_text
        .lines()
        .next()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty());
    cap.available = true;

    // P2：逐档位冒烟（**每个档位使用该档位合法的脚本**，见 `logic_sample`）
    for logic in CANDIDATE_LOGICS {
        if smoke_logic(b, logic, timeout) {
            cap.logics.insert((*logic).to_string());
        }
    }
    // `ALL`：允许全部理论的通用档位
    if smoke_logic(b, "ALL", timeout) {
        cap.logics.insert("ALL".to_string());
    }

    // P3：特性位（**在已实测支持的档位上探测**，避免用后端不支持的档位去问特性）
    cap.f_model = probe_over(b, &cap, FEATURE_CANDS, timeout, model_script, |p| {
        p.verdict() == Some(Verdict::Sat) && p.model().is_some_and(|m| !m.is_empty())
    });
    cap.f_unsat_core = probe_over(b, &cap, FEATURE_CANDS, timeout, core_script, |p| {
        p.verdict() == Some(Verdict::Unsat) && p.core().is_some_and(|c| !c.is_empty())
    });
    cap.f_incremental = probe_over(b, &cap, FEATURE_CANDS, timeout, incr_script, |p| {
        p.responses
            .iter()
            .filter(|x| matches!(x, crate::response::Response::Verdict(_)))
            .count()
            == 2
    });
    // `div`/`mod` 仅按 `Int` 族探测：本框架的除法线性化（`TH-4`）只对整数除法发射，
    // 故位向量后端的该位保守为 `false`（诚实刻画，避免路由器误判）。
    cap.f_div_mod = probe_over(b, &cap, INT_CANDS, timeout, divmod_script, |p| {
        p.verdict().is_some_and(Verdict::is_determinate)
    });
    // `re.inter` 属字串理论，只在字串档位上探测。
    cap.f_regex_inter = probe_over(b, &cap, STRING_CANDS, timeout, regex_script, |p| {
        p.verdict().is_some_and(Verdict::is_determinate)
    });
    cap.f_proof = probe_over(b, &cap, FEATURE_CANDS, timeout, proof_script, |p| {
        p.verdict() == Some(Verdict::Unsat)
    });
    // `Optimize` 扩展（供反例区间化，`06 §6.3.7`）：只用 `Int` 族探测——
    // 本框架的区间化只作用于连续排序，用位向量探测会把「BV 可优化」误记为「连续排序可优化」。
    cap.f_optimize = probe_optimize(b, &cap, timeout);
    cap
}

/// 探测 Optimize 扩展（`(minimize)`/`(maximize)` + `:opt.priority box`）。
///
/// 判据：`check-sat` 为 `sat`，**且**能从 `(get-objectives)` 中取回目标字段的值——
/// 后者是关键：部分求解器接受 `minimize` 语法却不返回目标（则区间化不可用）。
fn probe_optimize(b: &Backend, cap: &Capability, timeout: Duration) -> bool {
    for lg in INT_CANDS {
        if !cap.logics.contains(*lg) {
            continue;
        }
        let script = format!(
            "(set-logic {lg})\n(set-option :opt.priority box)\n\
             (declare-fun x () Int)\n(assert (>= x 0))\n(assert (<= x 10))\n\
             (minimize x)\n(maximize x)\n(check-sat)\n(get-objectives)\n"
        );
        let r = exec(b, &script, timeout);
        if r.timed_out || r.spawn_error.is_some() {
            continue;
        }
        let p = parse_responses(&r.stdout);
        if !p.unexpected_errors().is_empty() {
            continue;
        }
        if p.verdict() == Some(Verdict::Sat)
            && crate::interval::interval_from_objectives(&r.stdout, "x").is_some()
        {
            return true;
        }
    }
    false
}

/// 特性探测的**候选档位顺序**：先试 `Int` 族（本框架主用），再试位向量族，
/// 最后才用通用档位 `ALL`（`ALL` 最宽松，故放最后以免夸大能力）。
const FEATURE_CANDS: &[&str] = &[
    "QF_LIA", "QF_LIRA", "QF_LRA", "QF_BVLIA", "QF_BV", "QF_BVLRA", "QF_BVLIRA", "QF_SLIA", "ALL",
];

/// 仅 `Int` 族（用于 `div`/`mod`）。
const INT_CANDS: &[&str] = &["QF_LIA", "QF_LIRA", "QF_LRA", "QF_SLIA", "ALL"];

/// 仅字串族（用于 `re.inter`）。
const STRING_CANDS: &[&str] = &["QF_SLIA", "ALL"];

/// 在**后端已实测支持**的档位上依次尝试特性探测；任一成功即判该特性可用。
///
/// 逐档位而非固定单档位的原因：仅位向量的后端（bitwuzla）在 `QF_LIA` 下会直接拒绝，
/// 若用固定档位探测会把它的 `model`/`unsat-core` 等真实能力**误判为不支持**。
fn probe_over(
    b: &Backend,
    cap: &Capability,
    cands: &[&str],
    timeout: Duration,
    mk: fn(&str) -> Option<String>,
    check: impl Fn(&crate::response::ParsedOutput) -> bool,
) -> bool {
    for lg in cands {
        if !cap.logics.contains(*lg) {
            continue; // 该档位未被实测支持，跳过（不猜测）
        }
        let Some(script) = mk(lg) else { continue };
        let r = exec(b, &script, timeout);
        if r.timed_out || r.spawn_error.is_some() {
            continue;
        }
        let p = parse_responses(&r.stdout);
        if !p.unexpected_errors().is_empty() {
            continue; // 该档位下脚本被拒 ⇒ 换下一个档位
        }
        if check(&p) {
            return true;
        }
    }
    false
}

/// 该档位下「一个标量符号声明 + 一个可满足等式」。
fn scalar(lg: &str) -> (String, String) {
    if is_bv_family(lg) {
        (
            "(declare-fun b () (_ BitVec 8))\n".to_string(),
            "(= b (_ bv7 8))".to_string(),
        )
    } else {
        (
            "(declare-fun x () Int)\n".to_string(),
            "(= x 7)".to_string(),
        )
    }
}

/// 该档位是否属于位向量族（决定用 `BitVec` 还是 `Int` 造样例）。
fn is_bv_family(lg: &str) -> bool {
    matches!(lg, "QF_BV" | "QF_BVLIA" | "QF_BVLRA" | "QF_BVLIRA")
}

fn model_script(lg: &str) -> Option<String> {
    let (decl, eq) = scalar(lg);
    Some(format!(
        "(set-logic {lg})\n(set-option :produce-models true)\n{decl}\
         (assert {eq})\n(check-sat)\n(get-model)\n"
    ))
}

/// 一对**互斥**的具名断言（必然 `unsat`），用于核与证明探测。
fn core_script(lg: &str) -> Option<String> {
    let decl: String;
    let (a, b): (&str, &str) = if is_bv_family(lg) {
        decl = "(declare-fun b () (_ BitVec 8))\n".to_string();
        ("(= b (_ bv1 8))", "(= b (_ bv2 8))")
    } else {
        decl = "(declare-fun x () Int)\n".to_string();
        ("> x 10", "< x 5")
    };
    Some(format!(
        "(set-logic {lg})\n(set-option :produce-unsat-cores true)\n{decl}\
         (assert (! {a} :named A))\n(assert (! {b} :named B))\n(check-sat)\n(get-unsat-core)\n"
    ))
}

fn incr_script(lg: &str) -> Option<String> {
    let (decl, v1, v2): (&str, &str, &str) = if is_bv_family(lg) {
        (
            "(declare-fun b () (_ BitVec 8))\n",
            "(_ bv1 8)",
            "(_ bv2 8)",
        )
    } else {
        ("(declare-fun x () Int)\n", "1", "2")
    };
    let sym = if is_bv_family(lg) { "b" } else { "x" };
    Some(format!(
        "(set-logic {lg})\n{decl}\
         (push 1)\n(assert (= {sym} {v1}))\n(check-sat)\n\
         (pop 1)\n(assert (= {sym} {v2}))\n(check-sat)\n"
    ))
}

fn divmod_script(lg: &str) -> Option<String> {
    if is_bv_family(lg) {
        Some(format!(
            "(set-logic {lg})\n(declare-fun b () (_ BitVec 8))\n\
             (assert (= (bvudiv b (_ bv2 8)) (_ bv1 8)))\n(check-sat)\n"
        ))
    } else {
        Some(format!(
            "(set-logic {lg})\n(declare-fun x () Int)\n\
             (assert (= (div x 3) 2))\n(check-sat)\n"
        ))
    }
}

fn regex_script(lg: &str) -> Option<String> {
    Some(format!(
        "(set-logic {lg})\n(declare-fun s () String)\n\
         (assert (str.in_re s (re.inter (re.* re.allchar) (re.range \"a\" \"z\"))))\n\
         (check-sat)\n"
    ))
}

fn proof_script(lg: &str) -> Option<String> {
    // 复用「一对互斥具名断言」的骨架，替换选项与查询命令
    let base = core_script(lg)?;
    Some(
        base.replace(
            "(set-option :produce-unsat-cores true)",
            "(set-option :produce-proofs true)",
        )
        .replace("(get-unsat-core)", "(get-proof)"),
    )
}

/// 执行一次 stdin 投喂（统一走 [`crate::invocation::stdin_argv`] 合成命令行）。
///
/// **不要**在此处硬编码 argv：三款后端的 stdin 约定互不相同（`06 §6.5.1`）。
fn exec(b: &Backend, script: &str, timeout: Duration) -> ProcResult {
    let argv = crate::invocation::stdin_argv(&b.name, Some(timeout));
    run_captured_argv(&b.path, &argv, Some(script), timeout)
}

/// 某逻辑档位的**最小合法冒烟脚本**。
///
/// ## 为何必须按档位定制
/// 早期实现对**所有**档位投喂同一个「`Int` + `BitVec` + `String` + `re.inter`」单体脚本，
/// 于是 `QF_LIA` / `QF_BV` / `QF_UF` 等**必然失败**（脚本本身在该档位下不合法），
/// 只有 `ALL` 能通过——`ALG-3` 的能力矩阵实际退化为「后端是否支持 `ALL`」，
/// 与 `FR-17`「理论感知路由」的初衷相反。
///
/// 本函数为每个档位给出**只使用该档位允许理论**的脚本。`QF_BVLIA` / `QF_BVLRA` /
/// `QF_BVLIRA` 只要求「同时出现对应排序」而不要求二者真正混合——判定的是**档位是否可被接受**。
fn logic_sample(logic: &str) -> Option<String> {
    let s = match logic {
        "QF_UF" => {
            "(set-logic QF_UF)\n(declare-fun p () Bool)\n(declare-fun f (Bool) Bool)\n\
             (assert (f p))\n(check-sat)\n"
        }
        "QF_LIA" => {
            "(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (= (+ x 1) 3))\n(check-sat)\n"
        }
        "QF_LRA" => {
            "(set-logic QF_LRA)\n(declare-fun r () Real)\n\
             (assert (= (* r 2.0) 3.0))\n(check-sat)\n"
        }
        "QF_LIRA" => {
            "(set-logic QF_LIRA)\n(declare-fun x () Int)\n(declare-fun r () Real)\n\
             (assert (= (to_real x) r))\n(assert (> r 0.0))\n(check-sat)\n"
        }
        "QF_BV" => {
            "(set-logic QF_BV)\n(declare-fun b () (_ BitVec 8))\n\
             (assert (= (bvadd b (_ bv1 8)) (_ bv0 8)))\n(check-sat)\n"
        }
        "QF_BVLIA" => {
            "(set-logic QF_BVLIA)\n(declare-fun b () (_ BitVec 8))\n(declare-fun x () Int)\n\
             (assert (= b (_ bv7 8)))\n(assert (> x 0))\n(check-sat)\n"
        }
        "QF_BVLRA" => {
            "(set-logic QF_BVLRA)\n(declare-fun b () (_ BitVec 8))\n(declare-fun r () Real)\n\
             (assert (= b (_ bv7 8)))\n(assert (> r 0.0))\n(check-sat)\n"
        }
        "QF_BVLIRA" => {
            "(set-logic QF_BVLIRA)\n(declare-fun b () (_ BitVec 8))\n(declare-fun x () Int)\n\
             (declare-fun r () Real)\n(assert (= b (_ bv7 8)))\n\
             (assert (= (to_real x) r))\n(check-sat)\n"
        }
        "QF_SLIA" => {
            "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
             (assert (str.contains s \"a\"))\n(check-sat)\n"
        }
        "ALL" => {
            "(set-logic ALL)\n(declare-fun x () Int)\n(declare-fun b () (_ BitVec 8))\n\
             (declare-fun s () String)\n(assert (> x 0))\n(assert (= b (_ bv1 8)))\n\
             (assert (str.contains s \"a\"))\n(check-sat)\n"
        }
        _ => return None,
    };
    Some(s.to_string())
}

/// `P2`：单档位冒烟。
///
/// 判据：脚本**被接受且被求解**——判定为 `sat` 或 `unsat` 均可（二者都证明该档位可用），
/// 但 `unknown`、超时、启动失败、或任何 `(error …)` 都判为**不支持**（保守，`TH-3a`）。
fn smoke_logic(b: &Backend, logic: &str, timeout: Duration) -> bool {
    let Some(script) = logic_sample(logic) else {
        return false;
    };
    let r = exec(b, &script, timeout);
    if r.timed_out || r.spawn_error.is_some() {
        return false;
    }
    let p = parse_responses(&r.stdout);
    // `06 §6.8.3`：只把**未预期**错误视为不支持（预期错配须忽略）
    p.verdict().is_some_and(Verdict::is_determinate) && p.unexpected_errors().is_empty()
}

/// 探测全部后端。
pub fn probe_all(backends: &[Backend], timeout: Duration) -> Vec<Capability> {
    backends
        .iter()
        .map(|b| probe_backend(b, timeout))
        .collect()
}

/// 从 `PATH` 发现常见求解器（名称 → 可执行名）。
pub const DEFAULT_BACKENDS: &[(&str, &str)] = &[
    ("z3", "z3"),
    ("cvc5", "cvc5"),
    ("bitwuzla", "bitwuzla"),
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn missing_backend_is_unavailable_with_note() {
        let c = probe_backend(
            &Backend {
                name: "ghost".into(),
                path: "definitely-not-a-real-binary-xyz".into(),
            },
            Duration::from_millis(80),
        );
        assert!(!c.available);
        assert!(!c.notes.is_empty());
        assert!(!c.supports("QF_LIA"));
    }

    #[test]
    fn capability_json_is_wellformed() {
        let c = Capability::unavailable("z3", "z3", "not found");
        let j = capability_json(&[c]);
        assert!(j.starts_with('{'));
        assert!(j.contains("\"name\": \"z3\""));
        assert!(j.trim_end().ends_with('}'));
    }
}
