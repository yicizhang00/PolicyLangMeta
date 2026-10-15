//! `ALG-3` 后端能力探测（`FR-17`、`06 §6.4.3`，修正 `A-14`）。
//!
//! 把逻辑名从「硬编码」降级为**候选名**：实际支持度由**运行期实测**决定。
//! 未探测成功的能力一律保守为 `false`（探测失败即禁用该档位的 `Pass` 输出，`TH-3a`）。

use std::collections::BTreeSet;
use std::time::Duration;

use crate::orchestra::{run_captured, Backend};
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
        s.push_str(&format!("      \"f_proof\": {}\n", c.f_proof));
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

    // P2：逐档位冒烟
    for logic in CANDIDATE_LOGICS {
        if smoke_logic(&b.path, logic, timeout) {
            cap.logics.insert((*logic).to_string());
        }
    }
    // `ALL`：无 `set-logic` 的通用档位（多数求解器默认允许）
    if smoke_logic(&b.path, "ALL", timeout) {
        cap.logics.insert("ALL".to_string());
    }

    // P3：特性位
    cap.f_model = probe_model(&b.path, timeout);
    cap.f_unsat_core = probe_unsat_core(&b.path, timeout);
    cap.f_incremental = probe_incremental(&b.path, timeout);
    cap.f_div_mod = probe_div_mod(&b.path, timeout);
    cap.f_regex_inter = probe_regex_inter(&b.path, timeout);
    cap.f_proof = probe_proof(&b.path, timeout);
    cap
}

/// `P2`：单档位冒烟脚本。
fn smoke_logic(path: &str, logic: &str, timeout: Duration) -> bool {
    let script = format!(
        "(set-logic {logic})\n\
         (declare-fun pl_probe_int () Int)\n\
         (declare-fun pl_probe_bv  () (_ BitVec 8))\n\
         (declare-fun pl_probe_str () String)\n\
         (assert (= pl_probe_int 0))\n\
         (assert (= (bvand pl_probe_bv (_ bv1 8)) (_ bv1 8)))\n\
         (assert (str.in_re pl_probe_str (re.inter (re.* re.allchar) (re.range \"a\" \"z\"))))\n\
         (check-sat)\n"
    );
    let r = run_captured(path, &["-in"], Some(&script), timeout);
    if r.timed_out || r.spawn_error.is_some() {
        return false;
    }
    let p = parse_responses(&r.stdout);
    // 期望序列**首项**为 sat，且无 `(error …)`
    p.verdict() == Some(Verdict::Sat) && p.errors().is_empty()
}

fn probe_model(path: &str, timeout: Duration) -> bool {
    let script = "(set-logic QF_LIA)\n(set-option :produce-models true)\n\
                  (declare-fun x () Int)\n(assert (= x 7))\n(check-sat)\n(get-model)\n";
    let r = run_captured(path, &["-in"], Some(script), timeout);
    let p = parse_responses(&r.stdout);
    p.verdict() == Some(Verdict::Sat) && p.model().map(|m| !m.is_empty()).unwrap_or(false)
}

fn probe_unsat_core(path: &str, timeout: Duration) -> bool {
    let script = "(set-logic QF_LIA)\n(set-option :produce-unsat-cores true)\n\
                  (declare-fun x () Int)\n\
                  (assert (! (> x 10) :named A))\n(assert (! (< x 5) :named B))\n\
                  (check-sat)\n(get-unsat-core)\n";
    let r = run_captured(path, &["-in"], Some(script), timeout);
    let p = parse_responses(&r.stdout);
    p.verdict() == Some(Verdict::Unsat) && p.core().map(|c| !c.is_empty()).unwrap_or(false)
}

fn probe_incremental(path: &str, timeout: Duration) -> bool {
    let script = "(set-logic QF_LIA)\n(declare-fun x () Int)\n\
                  (push 1)\n(assert (= x 1))\n(check-sat)\n(pop 1)\n(assert (= x 2))\n(check-sat)\n";
    let r = run_captured(path, &["-in"], Some(script), timeout);
    let p = parse_responses(&r.stdout);
    // 期望**两次**判定
    let n = p
        .responses
        .iter()
        .filter(|x| matches!(x, crate::response::Response::Verdict(_)))
        .count();
    n == 2
}

fn probe_div_mod(path: &str, timeout: Duration) -> bool {
    let script = "(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (= (div x 3) 2))\n(check-sat)\n";
    let r = run_captured(path, &["-in"], Some(script), timeout);
    parse_responses(&r.stdout).verdict() == Some(Verdict::Sat)
}

fn probe_regex_inter(path: &str, timeout: Duration) -> bool {
    let script = "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                  (assert (str.in_re s (re.inter (re.* re.allchar) (re.range \"a\" \"z\"))))\n\
                  (check-sat)\n";
    let r = run_captured(path, &["-in"], Some(script), timeout);
    parse_responses(&r.stdout).verdict() == Some(Verdict::Sat)
}

fn probe_proof(path: &str, timeout: Duration) -> bool {
    let script = "(set-logic QF_LIA)\n(set-option :produce-proofs true)\n\
                  (declare-fun x () Int)\n(assert (! (> x 1) :named A))\n(assert (! (< x 0) :named B))\n\
                  (check-sat)\n(get-proof)\n";
    let r = run_captured(path, &["-in"], Some(script), timeout);
    let p = parse_responses(&r.stdout);
    p.verdict() == Some(Verdict::Unsat) && p.errors().is_empty()
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
