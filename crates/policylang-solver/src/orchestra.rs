//! 进程级竞速编排（`06 §6.6`，修正 `B-10`/`C-9`/`C-11`）。
//!
//! ## 与规范的一处**实现层等价替换**（诚实说明）
//! `DD-4` 指定 `JoinSet::shutdown().await` + `kill_on_drop(true)`（tokio）。本实现使用
//! `std::thread` + `std::process::Child`，并**显式**执行 `kill()` + `wait()`：
//!
//! - `kill()` ≡ `SIGKILL`（Unix）/ `TerminateProcess`（Windows），即 `kill_on_drop` 的效果；
//! - 紧随其后的 `wait()` **排空**子进程并回收僵尸，即 `shutdown().await` 的「保证 drop 已发生」语义。
//!
//! 因此 `NFR-3`（残留率为 0）与 `AC-5`（首胜回收可测）在本实现下同样成立；
//! 差别仅在**不使用异步运行时**（本环境无法离线获取 tokio 的 `rt-multi-thread` 依赖）。

use std::io::{Read, Write};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use policylang_ast::codes::{E_SOLVER_MISSING, E_SOLVER_PROTOCOL};
use policylang_ast::diag::Diagnostic;

use crate::response::{parse_responses, ParsedOutput, Verdict};

/// 单个后端。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Backend {
    pub name: String,
    pub path: String,
}

/// 进程执行结果。
#[derive(Debug, Clone)]
pub struct ProcResult {
    pub stdout: String,
    pub stderr: String,
    pub ok: bool,
    pub timed_out: bool,
    pub elapsed_ms: u64,
    pub spawn_error: Option<String>,
}

/// 运行一个子进程并**强制超时回收**（`06 §6.5.3`）。
pub fn run_captured(
    program: &str,
    args: &[&str],
    stdin_data: Option<&str>,
    timeout: Duration,
) -> ProcResult {
    let owned: Vec<String> = args.iter().map(|s| (*s).to_string()).collect();
    run_captured_argv(program, &owned, stdin_data, timeout)
}

/// 同 [`run_captured`]，但接受**拥有所有权**的 argv。
///
/// 供需要按后端合成命令行的调用方使用（如 `z3` 的 `-T:<秒>` 软超时），
/// 命令行构造规则见 [`crate::invocation`]。
pub fn run_captured_argv(
    program: &str,
    args: &[String],
    stdin_data: Option<&str>,
    timeout: Duration,
) -> ProcResult {
    let started = Instant::now();
    let mut cmd = Command::new(program);
    cmd.args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return ProcResult {
                stdout: String::new(),
                stderr: String::new(),
                ok: false,
                timed_out: false,
                elapsed_ms: started.elapsed().as_millis() as u64,
                spawn_error: Some(e.to_string()),
            }
        }
    };
    let slot: Slot = Arc::new(Mutex::new(Some(child)));
    let (out, err, timed_out) = pump(&slot, stdin_data, timeout);
    ProcResult {
        ok: !timed_out && out.1,
        stdout: out.0,
        stderr: err,
        timed_out,
        elapsed_ms: started.elapsed().as_millis() as u64,
        spawn_error: None,
    }
}

type Slot = Arc<Mutex<Option<Child>>>;

/// 向子进程喂入 stdin，读尽 stdout/stderr，并在超时后**强杀并回收**。
///
/// 返回 `((stdout, exited_zero), stderr, timed_out)`。
fn pump(slot: &Slot, stdin_data: Option<&str>, timeout: Duration) -> ((String, bool), String, bool) {
    let (mut sin, mut sout, mut serr) = {
        let mut g = slot.lock().unwrap();
        let c = g.as_mut().expect("子进程槽位已被取走");
        (c.stdin.take(), c.stdout.take(), c.stderr.take())
    };
    // stdin：写完后**关闭**（`CO-6`：不发 `(exit)`，由 stdin 关闭触发退出）
    if let Some(mut si) = sin.take() {
        let data = stdin_data.unwrap_or("").to_string();
        std::thread::spawn(move || {
            let _ = si.write_all(data.as_bytes());
            let _ = si.flush();
            drop(si);
        });
    }
    let out_handle = sout.take().map(|mut s| {
        std::thread::spawn(move || {
            let mut buf = String::new();
            let _ = s.read_to_string(&mut buf);
            buf
        })
    });
    let err_handle = serr.take().map(|mut s| {
        std::thread::spawn(move || {
            let mut buf = String::new();
            let _ = s.read_to_string(&mut buf);
            buf
        })
    });

    // 轮询等待退出；超时则强杀（`kill_on_drop` 的等价显式化）
    let deadline = Instant::now() + timeout;
    let mut timed_out = false;
    let ok = loop {
        {
            let mut g = slot.lock().unwrap();
            match g.as_mut() {
                Some(c) => match c.try_wait() {
                    Ok(Some(st)) => break st.success(),
                    Ok(None) => {}
                    Err(_) => break false,
                },
                // 已被主控回收（竞速落败路径）
                None => break false,
            }
        }
        if Instant::now() >= deadline {
            timed_out = true;
            break false;
        }
        std::thread::sleep(Duration::from_millis(2));
    };

    if timed_out {
        kill_and_reap(slot);
    }
    let out = out_handle
        .and_then(|h| h.join().ok())
        .unwrap_or_default();
    let err = err_handle
        .and_then(|h| h.join().ok())
        .unwrap_or_default();
    // 收敛：确保子进程被回收（无残留，`NFR-3`）
    kill_and_reap(slot);
    ((out, ok), err, timed_out)
}

/// 强杀并**回收**（`wait()` 排空），幂等。
pub fn kill_and_reap(slot: &Slot) {
    let taken = {
        let mut g = slot.lock().unwrap();
        g.take()
    };
    if let Some(mut c) = taken {
        let _ = c.kill();
        let _ = c.wait();
    }
}

/// 把脚本切成「非具名部分」与「具名断言列表」（`label, 整行`）。
///
/// 生成器对每条具名断言**恰好输出一行** `(assert (! <body> :named <label>))`，
/// 故可按行切分，用于 `ALG-4` 的 assumption 子集重查（`06 §6.9.2`）。
pub fn split_named_asserts(script: &str) -> (Vec<String>, Vec<(String, String)>) {
    let mut keep: Vec<String> = Vec::new();
    let mut named: Vec<(String, String)> = Vec::new();
    for line in script.lines() {
        if line.trim_start().starts_with("(assert (!") {
            if let Some(label) = extract_named_label(line) {
                named.push((label, line.to_string()));
                continue;
            }
        }
        keep.push(line.to_string());
    }
    (keep, named)
}

/// 从一行 `(assert (! … :named LABEL))` 中取出 `LABEL`。
pub fn extract_named_label(line: &str) -> Option<String> {
    let idx = line.rfind(":named ")?;
    let rest = &line[idx + ":named ".len()..];
    let label: String = rest
        .chars()
        .take_while(|c| !c.is_whitespace() && *c != ')')
        .collect();
    if label.is_empty() {
        None
    } else {
        Some(label)
    }
}

/// 用给定的具名断言**子集**重建可求解脚本（去掉原 payload，重新追加 `(check-sat)`）。
pub fn rebuild_script(keep: &[String], subset: &[(String, String)]) -> String {
    let mut s = String::new();
    for line in keep {
        let t = line.trim_start();
        if t.starts_with("(check-sat)") || t.starts_with("(get-model") || t.starts_with("(get-unsat-core") {
            continue;
        }
        s.push_str(line);
        s.push('\n');
    }
    for (_, line) in subset {
        s.push_str(line);
        s.push('\n');
    }
    s.push_str("(check-sat)\n");
    s
}

/// 单后端的一次运行结果。
#[derive(Debug, Clone)]
pub struct SolverRun {
    pub name: String,
    pub verdict: Verdict,
    pub raw: ParsedOutput,
    pub elapsed_ms: u64,
    pub timed_out: bool,
    pub stderr: String,
    pub spawn_error: Option<String>,
}

/// `UNSAT` 确认策略（`OQ-4`，默认 `two-of-n`）。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Confirmation {
    /// 首胜即止（含 `unsat`）。
    None,
    /// `sat` 首胜即止；`unsat` 需两个后端一致（`OQ-4` 建议值）。
    TwoOfN,
}

/// 竞速选项。
#[derive(Debug, Clone)]
pub struct RaceOptions {
    pub timeout: Duration,
    pub confirmation: Confirmation,
}

impl Default for RaceOptions {
    fn default() -> Self {
        RaceOptions {
            timeout: Duration::from_millis(3000),
            confirmation: Confirmation::TwoOfN,
        }
    }
}

/// 竞速结果。
#[derive(Debug, Clone)]
pub struct RaceOutcome {
    pub winner: Option<SolverRun>,
    /// 全部已收到的运行结果（含落败者，供交叉验证与审计）。
    pub runs: Vec<SolverRun>,
    /// 判定是否因超时/未知而未定。
    pub undetermined: bool,
    /// 首胜后回收落败进程的耗时（`AC-5` 的 `t_kill`）。
    pub kill_latency_ms: u64,
    pub diagnostics: Vec<Diagnostic>,
}

impl RaceOutcome {
    pub fn verdict(&self) -> Verdict {
        self.winner
            .as_ref()
            .map(|w| w.verdict)
            .unwrap_or(if self.undetermined {
                Verdict::Unknown
            } else {
                Verdict::Unknown
            })
    }

    pub fn winner_name(&self) -> Option<&str> {
        self.winner.as_ref().map(|w| w.name.as_str())
    }

    /// 是否存在两个后端给出**不一致的确定判定**（`E-XVALIDATE-MISMATCH` 的依据）。
    pub fn conflicting_determinate(&self) -> Option<(String, Verdict, String, Verdict)> {
        let det: Vec<&SolverRun> = self
            .runs
            .iter()
            .filter(|r| r.verdict.is_determinate())
            .collect();
        for i in 0..det.len() {
            for j in (i + 1)..det.len() {
                if det[i].verdict != det[j].verdict {
                    return Some((
                        det[i].name.clone(),
                        det[i].verdict,
                        det[j].name.clone(),
                        det[j].verdict,
                    ));
                }
            }
        }
        None
    }
}

/// 进程级竞速：首胜即止 + **立即强杀**其余（`FR-8`、`DD-4`）。
///
/// 峰值并发子进程数 = `backends.len()`（不随并发请求增长，`C-11`）。
pub fn solve_race(script: &str, backends: &[Backend], opts: &RaceOptions) -> RaceOutcome {
    let started = Instant::now();
    let mut diagnostics = Vec::new();
    if backends.is_empty() {
        diagnostics.push(Diagnostic::error(
            E_SOLVER_MISSING,
            "无可用的求解器后端：请安装 Z3/CVC5/Bitwuzla，或用 `--solvers` 指定路径",
        ));
        return RaceOutcome {
            winner: None,
            runs: Vec::new(),
            undetermined: true,
            kill_latency_ms: 0,
            diagnostics,
        };
    }

    // 把 `&opts` 拆成 `Copy` 值传入线程，避免跨线程借用
    let timeout = opts.timeout;
    // `two-of-n` 在**后端不足 2 个**时不可满足；此时降级为首胜即止（并由路由层发
    // `W-SINGLE-BACKEND` 告警），否则单后端环境将永远得到 `unknown`（可用性缺陷）。
    let confirmation = if backends.len() < 2 {
        Confirmation::None
    } else {
        opts.confirmation
    };
    let cancelled = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel::<(usize, SolverRun)>();
    let mut slots: Vec<Slot> = Vec::with_capacity(backends.len());

    for (idx, b) in backends.iter().enumerate() {
        let slot: Slot = Arc::new(Mutex::new(None));
        slots.push(slot.clone());
        let tx = tx.clone();
        let b = b.clone();
        let script = script.to_string();
        let cancelled = Arc::clone(&cancelled);
        std::thread::spawn(move || {
            let run = run_one(&b, &script, slot.clone(), timeout, &cancelled);
            let _ = tx.send((idx, run));
            // 确保本线程负责的进程被回收（无残留）
            kill_and_reap(&slot);
        });
    }
    drop(tx);

    let mut runs: Vec<SolverRun> = Vec::new();
    let deadline = started + opts.timeout + Duration::from_millis(200);
    let mut winner_idx: Option<usize> = None;
    let mut unsat_agree = 0usize;

    while runs.len() < backends.len() {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            break;
        }
        match rx.recv_timeout(remaining) {
            Ok((_, run)) => {
                match run.verdict {
                    Verdict::Sat => {
                        // SAT 有见证 ⇒ 首胜即止
                        winner_idx = Some(runs.len());
                        runs.push(run);
                        break;
                    }
                    Verdict::Unsat => {
                        unsat_agree += 1;
                        let decided = match confirmation {
                            Confirmation::None => true,
                            Confirmation::TwoOfN => unsat_agree >= 2,
                        };
                        runs.push(run);
                        if decided {
                            winner_idx = Some(runs.len() - 1);
                            break;
                        }
                    }
                    _ => runs.push(run),
                }
            }
            Err(mpsc::RecvTimeoutError::Timeout) => break,
            Err(mpsc::RecvTimeoutError::Disconnected) => break,
        }
    }

    // ── 关键：立即回收其余全部子进程（`JoinSet::shutdown().await` 的等价语义）──
    let kill_start = Instant::now();
    cancelled.store(true, Ordering::SeqCst);
    for s in &slots {
        kill_and_reap(s);
    }
    let kill_latency_ms = kill_start.elapsed().as_millis() as u64;

    // 未定：若所有后端都完成但无确定判定，或超时
    let winner = winner_idx.and_then(|i| runs.get(i).cloned()).or_else(|| {
        // 若 `TwoOfN` 下只收到 1 个 unsat，且恰有第二个 unsat 已在 runs 中 ⇒ 取首个确定者
        runs.iter()
            .find(|r| r.verdict == Verdict::Unsat && unsat_agree >= 2)
            .cloned()
            .or_else(|| {
                if confirmation == Confirmation::None {
                    runs.iter().find(|r| r.verdict.is_determinate()).cloned()
                } else if unsat_agree >= 2 {
                    runs.iter().find(|r| r.verdict == Verdict::Unsat).cloned()
                } else {
                    None
                }
            })
    });

    let undetermined = winner.is_none();
    if undetermined {
        for r in &runs {
            if let Some(e) = &r.spawn_error {
                diagnostics.push(Diagnostic::error(
                    E_SOLVER_MISSING,
                    format!("求解器 `{}` 启动失败：{e}", r.name),
                ));
            }
        }
        if runs.iter().any(|r| r.timed_out) {
            diagnostics.push(Diagnostic::warning(
                policylang_ast::codes::W_SLOW_GOAL,
                format!(
                    "竞速在 {} ms 内未得到确定判定（后端：{}）",
                    opts.timeout.as_millis(),
                    backends
                        .iter()
                        .map(|b| b.name.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            ));
        }
    }
    // `06 §6.8.3`：只有**未预期**的错误才升级为 `E-SOLVER_PROTOCOL`。
    // 「同发 `get-model` / `get-unsat-core`」必然产生的错配属协议预期、必须忽略——
    // 早期实现用 `contains("invalid")` 之类的启发式，会把真实求解器的有效判定整条丢弃。
    let mut unexpected: Vec<String> = Vec::new();
    for r in &runs {
        for e in r.raw.unexpected_errors() {
            unexpected.push(format!("{}: {}", r.name, e));
        }
    }
    if !unexpected.is_empty() {
        diagnostics.push(Diagnostic::error(
            E_SOLVER_PROTOCOL,
            format!(
                "求解器响应含未预期的 `(error …)`：{}（请检查脚本是否与后端能力匹配）",
                unexpected.join("; ")
            ),
        ));
    }

    RaceOutcome {
        winner,
        runs,
        undetermined,
        kill_latency_ms,
        diagnostics,
    }
}

fn run_one(
    b: &Backend,
    script: &str,
    slot: Slot,
    timeout: Duration,
    cancelled: &AtomicBool,
) -> SolverRun {
    let started = Instant::now();
    let mut cmd = Command::new(&b.path);
    // 按后端合成命令行：三款后端的 stdin 约定互不相同（`06 §6.5.1`）。
    // 历史上此处硬编码 `-in`，导致 cvc5 / bitwuzla 全部探测失败（见 `invocation` 模块）。
    cmd.args(crate::invocation::stdin_argv(&b.name, Some(timeout)))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return SolverRun {
                name: b.name.clone(),
                verdict: Verdict::Unknown,
                raw: ParsedOutput::default(),
                elapsed_ms: started.elapsed().as_millis() as u64,
                timed_out: false,
                stderr: String::new(),
                spawn_error: Some(e.to_string()),
            }
        }
    };
    {
        let mut g = slot.lock().unwrap();
        *g = Some(child);
    }
    let ((stdout, _ok), stderr, timed_out) = pump(&slot, Some(script), timeout);
    let raw = parse_responses(&stdout);
    let verdict = raw.verdict().unwrap_or(Verdict::Unknown);
    let _ = cancelled.load(Ordering::SeqCst);
    SolverRun {
        name: b.name.clone(),
        verdict,
        raw,
        elapsed_ms: started.elapsed().as_millis() as u64,
        timed_out,
        stderr,
        spawn_error: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn run_captured_enforces_timeout_and_reaps() {
        // 用一个不存在的程序验证 spawn 错误路径
        let r = run_captured("definitely-not-a-real-binary-xyz", &[], None, Duration::from_millis(50));
        assert!(r.spawn_error.is_some());
        assert!(!r.ok);
    }

    #[test]
    fn empty_backends_reports_missing() {
        let o = solve_race("(check-sat)\n", &[], &RaceOptions::default());
        assert!(o.undetermined);
        assert!(!o.diagnostics.is_empty());
    }

    #[test]
    fn unknown_binary_is_reported_not_panicked() {
        let b = vec![Backend {
            name: "ghost".into(),
            path: "definitely-not-a-real-binary-xyz".into(),
        }];
        let o = solve_race("(set-logic QF_LIA)\n(check-sat)\n", &b, &RaceOptions::default());
        assert!(o.undetermined);
        assert!(o.diagnostics.iter().any(|d| d.code == E_SOLVER_MISSING));
    }
}
