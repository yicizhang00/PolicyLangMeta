//! 各求解器的**命令行约定**（`06 §6.5.1`）。
//!
//! ## 为什么需要模块化：三款后端的 stdin 调用方式**互不相同**
//!
//! 实测结论（本机 z3 5.3.0 / cvc5 1.4.2 / bitwuzla 0.9.1）：
//!
//! | 后端 | 正确 argv | 错误 argv 的实际后果 |
//! |---|---|---|
//! | `z3` | `-in -smt2` | — |
//! | `cvc5` | `--lang=smt2 --incremental` | `-in` ⇒ `Error in option parsing: can't understand option '-in'`（全部探测失败） |
//! | `bitwuzla` | `--lang=smt2` | `-` ⇒ `invalid option '-'`；`-in` ⇒ 同类解析错误 |
//!
//! 早期实现把 `-in` 硬编码给所有后端，结果**只有 z3 能工作**：cvc5/bitwuzla 的
//! `ALG-3` 探测全为否、档位集合为空。这是**只有在真实求解器在场时才会暴露**的缺陷——
//! 测试替身对 argv 不敏感，因此离线阶段无法发现。
//!
//! `cvc5` 的 `--incremental` 不可省略：实测 `(push 1)` 在非增量模式下报
//! `cannot push when not solving incrementally`，会使 `FR-9`/`CO-4` 的增量通道与
//! `probe_incremental` 全部失败。规范 `06 §6.5.1` 已列出该参数。

use std::time::Duration;

/// 该后端的**从 stdin 读取 SMT-LIB2** 的命令行参数。
///
/// `soft_timeout` 为 `Some` 时，对支持**软超时开关**的后端（当前仅 `z3` 的 `-T:<秒>`）追加该参数：
/// 让求解器有机会**优雅返回 `unknown`**，而不是只能被宿主强杀（`06 §6.4.4` / `§6.6.4`）。
/// 秒数**向上取整且至少 1**，避免亚秒超时被截断为 0 而导致立即放弃。
///
/// 未知后端返回空 argv（按「裸 stdin」约定），以便第三方后端仍可被 `--solvers NAME=PATH` 接入。
pub fn stdin_argv(name: &str, soft_timeout: Option<Duration>) -> Vec<String> {
    match name {
        "z3" => {
            let mut v = vec!["-in".to_string(), "-smt2".to_string()];
            if let Some(t) = soft_timeout {
                let secs = t.as_millis().div_ceil(1000).max(1);
                v.push(format!("-T:{secs}"));
            }
            v
        }
        "cvc5" => vec!["--lang=smt2".to_string(), "--incremental".to_string()],
        "bitwuzla" => vec!["--lang=smt2".to_string()],
        _ => Vec::new(),
    }
}

/// 该后端是否支持 `(get-proof)`（`06 §6.7.2` 的证明检查前置条件）。
///
/// 仅作为**候选**判断，最终以 `ALG-3` 的 `f_proof` 实测为准（`TH-3a`：探测失败即禁用）。
pub fn proof_hint(name: &str) -> bool {
    matches!(name, "z3" | "cvc5")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cvc5_never_receives_dash_in() {
        // 回归锚定：`-in` 会使 cvc5 直接报选项解析错误
        let a = stdin_argv("cvc5", None);
        assert_eq!(a, vec!["--lang=smt2", "--incremental"]);
        assert!(!a.iter().any(|x| x == "-in" || x == "-"));
    }

    #[test]
    fn bitwuzla_uses_lang_flag_only() {
        assert_eq!(stdin_argv("bitwuzla", None), vec!["--lang=smt2"]);
    }

    #[test]
    fn z3_soft_timeout_is_ceil_and_at_least_one() {
        assert_eq!(
            stdin_argv("z3", Some(Duration::from_millis(1500))),
            vec!["-in", "-smt2", "-T:2"]
        );
        assert_eq!(
            stdin_argv("z3", Some(Duration::from_millis(10))),
            vec!["-in", "-smt2", "-T:1"]
        );
        assert_eq!(stdin_argv("z3", None), vec!["-in", "-smt2"]);
    }

    #[test]
    fn unknown_backend_falls_back_to_bare_stdin() {
        assert!(stdin_argv("mystery-solver", Some(Duration::from_secs(3))).is_empty());
    }

    #[test]
    fn argv_never_contains_the_universal_dash_in_for_non_z3() {
        for n in ["cvc5", "bitwuzla", "mystery"] {
            assert!(
                !stdin_argv(n, None).iter().any(|x| x == "-in"),
                "`{n}` 不应收到 `-in`"
            );
        }
    }
}
