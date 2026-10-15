//! `pl-stub-solver` —— **仅用于流水线测试的桩求解器**（**不是**真求解器）。
//!
//! ## 为什么需要它
//! 本环境未安装 Z3/CVC5/Bitwuzla。若没有它，只能验证「无求解器 ⇒ `E-SOLVER-MISSING` ⇒ exit 4」
//! 这一条路径，无法端到端验证「路由 → 竞速 → 响应流解析 → 模型/Core 还原 → 报告装配 → 退出码」。
//! 它是**测试替身（test double）**，仅在集成测试中通过 `--solvers stub=<路径>` 挂载。
//!
//! ## 行为（由环境变量控制）
//! - `PL_STUB_VERDICT`：`sat`（默认）/ `unsat` / `unknown` / `error`
//! - `PL_STUB_DELAY_MS`：响应前的延时（用于验证超时与首胜强杀）
//! - `PL_STUB_NAME`：`--version` 时回显的名字（用于区分竞速中的多个实例）
//!
//! 对 `sat` 依据脚本中的 `(declare-fun NAME () SORT)` 生成**结构完整**的模型；
//! 对 `unsat` 回显脚本中前两个 `:named` 标签作为 Unsat Core。

use std::io::{Read, Write};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--version") {
        println!(
            "{} stub-solver 0.1 (pipeline test double)",
            std::env::var("PL_STUB_NAME").unwrap_or_else(|_| "stub".into())
        );
        return;
    }

    let mut script = String::new();
    let _ = std::io::stdin().read_to_string(&mut script);

    if let Ok(ms) = std::env::var("PL_STUB_DELAY_MS") {
        if let Ok(n) = ms.parse::<u64>() {
            std::thread::sleep(std::time::Duration::from_millis(n));
        }
    }

    // 能力探测（`ALG-3`）脚本以 `pl_probe_` 前缀声明探针符号：此类脚本**恒答 sat**，
    // 模拟「真求解器按语义回答」的行为（否则探测结果会被 `PL_STUB_VERDICT` 污染，路由失效）。
    let probing = script.contains("pl_probe_");
    let verdict = if probing {
        "sat".to_string()
    } else {
        std::env::var("PL_STUB_VERDICT").unwrap_or_else(|_| "sat".into())
    };
    let check_sats = script.matches("(check-sat)").count().max(1);
    let mut out = String::new();
    if probing {
        for _ in 0..check_sats {
            out.push_str("sat\n");
        }
        out.push_str("(model\n");
        for (name, sort) in extract_decls(&script) {
            out.push_str(&format!("  (define-fun {name} () {sort} {})\n", zero_of(&sort)));
        }
        out.push_str(")\n");
        let _ = std::io::stdout().write_all(out.as_bytes());
        return;
    }
    match verdict.as_str() {
        "unsat" => {
            out.push_str("unsat\n");
            let labels = extract_named(&script);
            out.push('(');
            out.push_str(&labels.into_iter().take(2).collect::<Vec<_>>().join(" "));
            out.push_str(")\n");
        }
        "unknown" => out.push_str("unknown\n"),
        "error" => out.push_str("(error \"stub error\")\n"),
        _ => {
            out.push_str("sat\n");
            out.push_str("(model\n");
            for (name, sort) in extract_decls(&script) {
                out.push_str(&format!("  (define-fun {name} () {sort} {})\n", zero_of(&sort)));
            }
            out.push_str(")\n");
        }
    }
    let _ = std::io::stdout().write_all(out.as_bytes());
}

fn extract_named(s: &str) -> Vec<String> {
    let mut v = Vec::new();
    for line in s.lines() {
        if let Some(i) = line.rfind(":named ") {
            let rest = &line[i + 7..];
            let lab: String = rest
                .chars()
                .take_while(|c| !c.is_whitespace() && *c != ')')
                .collect();
            if !lab.is_empty() {
                v.push(lab);
            }
        }
    }
    v
}

fn extract_decls(s: &str) -> Vec<(String, String)> {
    let mut v = Vec::new();
    for line in s.lines() {
        let l = line.trim();
        if let Some(rest) = l.strip_prefix("(declare-fun ") {
            // 形如 `NAME () SORT)`：先剥掉最外层 `)`，再以 `()` 为界切分
            let body = rest.trim_end().strip_suffix(')').unwrap_or(rest).trim();
            if let Some(idx) = body.find("()") {
                let name = body[..idx].trim();
                let sort = body[idx + 2..].trim();
                if !name.is_empty() && !sort.is_empty() {
                    v.push((name.to_string(), sort.to_string()));
                }
            }
        }
    }
    v
}

fn zero_of(sort: &str) -> String {
    match sort {
        "Bool" => "true".into(),
        "Real" => "0.0".into(),
        "String" => "\"\"".into(),
        s if s.starts_with("(_ BitVec") => {
            let w = s
                .trim_start_matches("(_ BitVec")
                .trim_end_matches(')')
                .trim()
                .parse::<u32>()
                .unwrap_or(32);
            format!("(_ bv0 {w})")
        }
        _ => "0".into(),
    }
}
