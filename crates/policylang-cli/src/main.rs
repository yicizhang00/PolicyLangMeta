//! `policylang` —— PolicyLang Meta 命令行工具与 CI 门禁入口（CR-8，`IF-1`）。
//!
//! 子命令（`01 §4` 的 `IF-1` 契约）：
//! `verify`（全链路验证）/ `check`（仅静态检查）/ `fmt`（规范化）/ `diff`（策略精化对比）/
//! `solvers`（`ALG-3` 能力矩阵）/ `explain`（解释某目标）/ `init`（脚手架）/ `version`。
//!
//! 退出码恒为 5 个：`0` Pass/Waived · `1` Fail · `2` 转人工 · `3` 编译错误 · `4` 内部错误。

mod cmd_verify;
mod exit;

use std::path::PathBuf;
use std::time::Duration;

use policylang_check::CheckOptions;
use policylang_governance::ExitCode;
use policylang_solver::Confirmation;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let code = dispatch(&args);
    exit::exit_with(code);
}

fn dispatch(args: &[String]) -> ExitCode {
    let Some(cmd) = args.first().map(String::as_str) else {
        print_usage();
        return ExitCode::InternalError;
    };
    let rest = &args[1..];
    match cmd {
        "verify" => cmd_verify::run(&match parse_verify(rest) {
            Ok(o) => o,
            Err(m) => return exit::usage_error(&m),
        }),
        "check" => cmd_check(rest),
        "fmt" => cmd_fmt(rest),
        "diff" => cmd_diff(rest),
        "solvers" => cmd_solvers(rest),
        "explain" => cmd_explain(rest),
        "init" => cmd_init(rest),
        "version" | "--version" | "-V" => {
            println!("policylang {} (schema 1.0)", env!("CARGO_PKG_VERSION"));
            ExitCode::Pass
        }
        "help" | "--help" | "-h" => {
            print_usage();
            ExitCode::Pass
        }
        other => exit::usage_error(&format!("未知子命令 `{other}`（参见 `policylang help`）")),
    }
}

fn print_usage() {
    println!(
        "policylang {} — 策略语言定义、可判定性编译与形式化验证\n\
\n\
用法：policylang <子命令> [选项] [文件...]\n\
\n\
子命令：\n\
  verify   <file.plm...>   解析 → 检查 → 生成 → 求解 → 报告（退出码 0–4）\n\
  check    <file.plm...>   仅静态检查与可判定性守卫（不求解）\n\
  fmt      <file.plm...>   源码规范化（--write 就地写回）\n\
  diff     --new A --old B <file.plm>   策略精化四态对比\n\
  solvers                  列出 ALG-3 实测能力矩阵\n\
  explain  --goal <名> <file.plm>       解释某验证目标\n\
  init     [目录]          生成 policylang.toml 与示例\n\
  version / help\n\
\n\
verify 选项：\n\
  --timeout <ms>           单目标求解超时（默认 3000）\n\
  --output <file.json>     写入审计报告\n\
  --sarif <file.sarif>     写入 SARIF 2.1.0\n\
  --emit-smt <dir>         导出 SMT-LIB2 脚本\n\
  --emit-ast <file.json>   导出 AST\n\
  --emit-capability <file.json>  导出能力矩阵\n\
  --solvers <name[=path],...>    指定后端\n\
  --exclude-solver <name>  排除后端\n\
  --no-race                单后端（不做竞速）\n\
  --confirmation <none|two-of-n> UNSAT 确认策略（默认 two-of-n）\n\
  --no-minimize-core       关闭 Unsat Core 最小化\n\
  --minimize-budget <n>    最小化重查预算（默认 64）\n\
  --max-groundings <n>     展开预算 G_max（默认 1000000）\n\
  --allow-nonlinear        放行非线性（OQ-5 建议删除；目标将强制转人工）\n\
  --strict-logic           档位回落即报错（exit 4）\n\
  --mutex-max-pairs <n>    mutex 分支对数上限（默认 64）\n\
  --regex-budget <n>       单条正则转译预算（默认 4096）\n\
  --goal-parallelism <n>   目标级并行度（默认 1）\n\
  --quiet                  不打印人类可读摘要"
        ,
        env!("CARGO_PKG_VERSION")
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 选项解析
// ═════════════════════════════════════════════════════════════════════════════

fn parse_verify(args: &[String]) -> Result<cmd_verify::VerifyOptions, String> {
    let mut o = cmd_verify::VerifyOptions::default();
    let mut files: Vec<PathBuf> = Vec::new();
    let mut solver_names: Vec<String> = Vec::new();
    let mut exclude: Vec<String> = Vec::new();
    let mut i = 0usize;
    while i < args.len() {
        let a = args[i].as_str();
        let next = |i: &mut usize| -> Result<String, String> {
            *i += 1;
            args.get(*i)
                .cloned()
                .ok_or_else(|| format!("选项 `{a}` 缺少取值"))
        };
        match a {
            "--timeout" => {
                let v = next(&mut i)?;
                let ms: u64 = v.parse().map_err(|_| format!("--timeout 期望毫秒整数，得到 `{v}`"))?;
                if ms == 0 {
                    return Err("--timeout 必须 > 0（E-TIMEOUT-CONFIG）".into());
                }
                o.timeout = Duration::from_millis(ms);
            }
            "--output" => o.output = Some(PathBuf::from(next(&mut i)?)),
            "--sarif" => o.sarif = Some(PathBuf::from(next(&mut i)?)),
            "--emit-smt" => o.emit_smt_dir = Some(PathBuf::from(next(&mut i)?)),
            "--emit-ast" => o.emit_ast = Some(PathBuf::from(next(&mut i)?)),
            "--emit-capability" => o.emit_capability = Some(PathBuf::from(next(&mut i)?)),
            "--solvers" => {
                solver_names = next(&mut i)?
                    .split(',')
                    .filter(|s| !s.trim().is_empty())
                    .map(|s| s.trim().to_string())
                    .collect();
            }
            "--exclude-solver" => exclude.push(next(&mut i)?),
            "--no-race" => {
                o.confirmation = Confirmation::None;
                // 单后端：只保留第一个
                if solver_names.is_empty() {
                    solver_names = vec!["z3".to_string()];
                } else {
                    solver_names.truncate(1);
                }
            }
            "--confirmation" => {
                let v = next(&mut i)?;
                o.confirmation = match v.as_str() {
                    "none" => Confirmation::None,
                    "two-of-n" => Confirmation::TwoOfN,
                    _ => return Err(format!("--confirmation 只接受 none|two-of-n，得到 `{v}`")),
                };
            }
            "--no-minimize-core" => o.minimize_core = false,
            "--minimize-budget" => {
                o.minimize_budget = next(&mut i)?
                    .parse()
                    .map_err(|_| "--minimize-budget 期望整数".to_string())?;
            }
            "--max-groundings" => {
                o.check.max_groundings = next(&mut i)?
                    .parse()
                    .map_err(|_| "--max-groundings 期望整数".to_string())?;
            }
            "--allow-nonlinear" => o.check.allow_nonlinear = true,
            "--strict-logic" => o.check.strict_logic = true,
            "--mutex-max-pairs" => {
                o.check.mutex_max_pairs = next(&mut i)?
                    .parse()
                    .map_err(|_| "--mutex-max-pairs 期望整数".to_string())?;
            }
            "--regex-budget" => {
                o.check.regex_budget = next(&mut i)?
                    .parse()
                    .map_err(|_| "--regex-budget 期望整数".to_string())?;
            }
            "--goal-parallelism" => {
                o.goal_parallelism = next(&mut i)?
                    .parse::<usize>()
                    .map_err(|_| "--goal-parallelism 期望整数".to_string())?
                    .max(1);
            }
            "--quiet" => o.quiet = true,
            other if other.starts_with("--") => {
                return Err(format!("未知选项 `{other}`（参见 `policylang help`）"))
            }
            f => files.push(PathBuf::from(f)),
        }
        i += 1;
    }
    o.files = files;
    o.exclude_solvers = exclude;
    if !solver_names.is_empty() {
        o.solvers = cmd_verify::backends_from(&solver_names);
    }
    Ok(o)
}

fn files_of(args: &[String]) -> (Vec<PathBuf>, Vec<String>) {
    let mut files = Vec::new();
    let mut flags = Vec::new();
    for a in args {
        if a.starts_with('-') {
            flags.push(a.clone());
        } else {
            files.push(PathBuf::from(a));
        }
    }
    (files, flags)
}

// ═════════════════════════════════════════════════════════════════════════════
// check
// ═════════════════════════════════════════════════════════════════════════════

fn cmd_check(args: &[String]) -> ExitCode {
    let (files, flags) = files_of(args);
    if files.is_empty() {
        return exit::usage_error("check 需要至少一个 `.plm` 文件");
    }
    let mut opts = CheckOptions::default();
    if flags.iter().any(|f| f == "--allow-nonlinear") {
        opts.allow_nonlinear = true;
    }
    let mut have_error = false;
    for f in &files {
        let src = match std::fs::read_to_string(f) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("policylang: 无法读取 {}：{e}", f.display());
                return ExitCode::CompileError;
            }
        };
        let spec = match policylang_parser::parse_spec(&src, f.to_str()) {
            Ok(s) => s,
            Err(diags) => {
                for d in &diags {
                    eprintln!("{}", d.render());
                }
                have_error = true;
                continue;
            }
        };
        match policylang_check::check(&spec, &opts) {
            Ok(checked) => {
                println!(
                    "{}: 检查通过（逻辑档位: {}）",
                    f.display(),
                    checked
                        .policy_profiles
                        .iter()
                        .map(|(k, v)| format!("{k}={}", v.candidate_logic()))
                        .collect::<Vec<_>>()
                        .join(" ")
                );
                for d in &checked.warnings {
                    println!("  {}", d.render());
                }
            }
            Err(diags) => {
                have_error = true;
                for d in &diags {
                    eprintln!("{}", d.render());
                }
            }
        }
    }
    if have_error {
        ExitCode::CompileError
    } else {
        ExitCode::Pass
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// fmt
// ═════════════════════════════════════════════════════════════════════════════

fn cmd_fmt(args: &[String]) -> ExitCode {
    let (files, flags) = files_of(args);
    let write = flags.iter().any(|f| f == "--write" || f == "-w");
    if files.is_empty() {
        return exit::usage_error("fmt 需要至少一个 `.plm` 文件");
    }
    for f in &files {
        let src = match std::fs::read_to_string(f) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("policylang: 无法读取 {}：{e}", f.display());
                return ExitCode::CompileError;
            }
        };
        // 先确保语法有效（fmt 不得产出无法解析的文本）
        if let Err(diags) = policylang_parser::parse_spec(&src, f.to_str()) {
            for d in &diags {
                eprintln!("{}", d.render());
            }
            return ExitCode::CompileError;
        }
        let canon = policylang_governance::canon_src(&src);
        if write {
            if let Err(e) = std::fs::write(f, &canon) {
                eprintln!("policylang: 写入 {} 失败：{e}", f.display());
                return ExitCode::InternalError;
            }
            println!("已规范化 {}", f.display());
        } else {
            print!("{canon}");
        }
    }
    ExitCode::Pass
}

// ═════════════════════════════════════════════════════════════════════════════
// diff（策略精化四态）
// ═════════════════════════════════════════════════════════════════════════════

fn cmd_diff(args: &[String]) -> ExitCode {
    let mut new_p = None;
    let mut old_p = None;
    let mut file: Option<PathBuf> = None;
    let mut passthrough: Vec<String> = Vec::new();
    let mut i = 0usize;
    while i < args.len() {
        match args[i].as_str() {
            "--new" => {
                i += 1;
                new_p = args.get(i).cloned();
            }
            "--old" => {
                i += 1;
                old_p = args.get(i).cloned();
            }
            // 透传给 verify 的选项（含其取值）
            "--solvers" | "--timeout" | "--exclude-solver" | "--confirmation" | "--minimize-budget"
            | "--max-groundings" | "--mutex-max-pairs" | "--regex-budget" | "--goal-parallelism" => {
                passthrough.push(args[i].clone());
                i += 1;
                if let Some(v) = args.get(i) {
                    passthrough.push(v.clone());
                }
            }
            f if f.starts_with('-') => passthrough.push(f.to_string()),
            f => file = Some(PathBuf::from(f)),
        }
        i += 1;
    }
    let (Some(np), Some(op), Some(path)) = (new_p, old_p, file) else {
        return exit::usage_error("diff 需要 --new <策略> --old <策略> <file.plm>");
    };
    let src = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("policylang: 无法读取 {}：{e}", path.display());
            return ExitCode::CompileError;
        }
    };
    // 把 `refines` 目标追加上去，复用完整管线
    let extra = format!(
        "\nverify {np} refines {op}\n"
    );
    let dir = std::env::temp_dir().join(format!("policylang-diff-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let tmp = dir.join("diff.plm");
    if std::fs::write(&tmp, format!("{src}{extra}")).is_err() {
        return ExitCode::InternalError;
    }
    let mut o = match parse_verify(&passthrough) {
        Ok(o) => o,
        Err(m) => return exit::usage_error(&m),
    };
    o.files = vec![tmp];
    let code = cmd_verify::run(&o);
    let _ = std::fs::remove_dir_all(&dir);
    code
}

// ═════════════════════════════════════════════════════════════════════════════
// solvers（ALG-3）
// ═════════════════════════════════════════════════════════════════════════════

fn cmd_solvers(args: &[String]) -> ExitCode {
    let names: Vec<String> = args
        .iter()
        .filter(|a| !a.starts_with('-'))
        .map(|s| s.trim().to_string())
        .collect();
    let backends = cmd_verify::backends_from(&names);
    let caps = policylang_solver::probe_all(&backends, Duration::from_millis(1500));
    println!("{:<10} {:<8} {:<28} {}", "后端", "可用", "版本", "实测档位");
    for c in &caps {
        println!(
            "{:<10} {:<8} {:<28} {}",
            c.name,
            if c.available { "yes" } else { "no" },
            c.version.as_deref().unwrap_or("-"),
            if c.logics.is_empty() {
                "-".to_string()
            } else {
                c.logics.iter().cloned().collect::<Vec<_>>().join(",")
            }
        );
        for n in &c.notes {
            println!("    note: {n}");
        }
    }
    println!(
        "\n特性位：model / unsat-core / incremental / div-mod / re.inter / proof"
    );
    for c in &caps {
        println!(
            "{:<10} {:>5} {:>10} {:>11} {:>8} {:>11} {:>6}",
            c.name,
            yn(c.f_model),
            yn(c.f_unsat_core),
            yn(c.f_incremental),
            yn(c.f_div_mod),
            yn(c.f_regex_inter),
            yn(c.f_proof)
        );
    }
    println!("\n基线参考（06 §6.4.4，须以实测为准）：");
    for (name, ok, probe) in policylang_solver::BASELINE_MATRIX {
        println!("  {name}: 支持 {ok:?}；须探测 {probe:?}");
    }
    ExitCode::Pass
}

fn yn(b: bool) -> &'static str {
    if b {
        "yes"
    } else {
        "no"
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// explain
// ═════════════════════════════════════════════════════════════════════════════

fn cmd_explain(args: &[String]) -> ExitCode {
    let mut goal = None;
    let mut file = None;
    let mut i = 0usize;
    while i < args.len() {
        match args[i].as_str() {
            "--goal" => {
                i += 1;
                goal = args.get(i).cloned();
            }
            "--list" => goal = Some("__list__".to_string()),
            f => file = Some(PathBuf::from(f)),
        }
        i += 1;
    }
    let Some(path) = file else {
        return exit::usage_error("explain 需要 <file.plm>（可用 --list 列出目标）");
    };
    let src = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("policylang: 无法读取 {}：{e}", path.display());
            return ExitCode::CompileError;
        }
    };
    let (checked, out) = match cmd_verify::static_only(&src, &CheckOptions::default()) {
        Ok(x) => x,
        Err(diags) => {
            for d in &diags {
                eprintln!("{}", d.render());
            }
            return ExitCode::CompileError;
        }
    };
    let list = cmd_verify::goal_summary(&checked.spec);
    if goal.as_deref() == Some("__list__") || goal.is_none() {
        println!("验证目标（{} 条）：", list.len());
        for (name, t) in &list {
            println!("  {name}   [{t}]");
        }
        return ExitCode::Pass;
    }
    let g = goal.unwrap();
    let Some(q) = out.queries.iter().find(|q| q.goal_name.contains(&g)) else {
        eprintln!("policylang: 未找到目标 `{g}`（可用 --list 查看）");
        return ExitCode::InternalError;
    };
    println!("目标        : {}", q.goal_name);
    println!("类型        : {}", q.target_type.as_str());
    println!("逻辑档位    : {}", q.logic);
    println!(
        "期望判定    : {}",
        match q.expected {
            policylang_codegen::ExpectedVerdict::Sat => "sat ⇒ Pass",
            policylang_codegen::ExpectedVerdict::Unsat => "unsat ⇒ Pass",
        }
    );
    println!(
        "反证断言    : {}",
        q.refutation_label.as_deref().unwrap_or("(无)")
    );
    println!(":named 标签 : {}", q.labels.join(", "));
    if !q.notes.is_empty() {
        println!("备注        : {}", q.notes.join("; "));
    }
    println!("—— SMT-LIB2 ——");
    println!("{}", q.canonical());
    ExitCode::Pass
}

// ═════════════════════════════════════════════════════════════════════════════
// init
// ═════════════════════════════════════════════════════════════════════════════

fn cmd_init(args: &[String]) -> ExitCode {
    let dir = args
        .iter()
        .find(|a| !a.starts_with('-'))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));
    let _ = std::fs::create_dir_all(&dir);
    let cfg = dir.join("policylang.toml");
    if cfg.exists() {
        eprintln!("policylang: {} 已存在，未覆盖", cfg.display());
        return ExitCode::InternalError;
    }
    let toml = r#"# policylang.toml —— 项目配置（IF-4）
[project]
name = "my-policies"
specs = ["policies/*.plm"]

[verify]
timeout_ms = 3000
max_groundings = 1000000
mutex_max_pairs = 64
regex_budget = 4096
confirmation = "two-of-n"
minimize_core = true
minimize_budget = 64

[solvers]
names = ["z3", "cvc5", "bitwuzla"]
"#;
    if let Err(e) = std::fs::write(&cfg, toml) {
        eprintln!("policylang: 写入 {} 失败：{e}", cfg.display());
        return ExitCode::InternalError;
    }
    let example = dir.join("example.plm");
    let _ = std::fs::write(
        &example,
        r#"#lang policylang 2

entity Service {
    @key id: Int [min: 1, max: 100],
    host_ip: IPv4,
    port: Int [min: 1, max: 65535]
}

domain Services: Set[Service] [size: 4]

policy DeploymentPolicy {
    rule NoPortConflict:
        forall s1, s2 in Services:
            (s1.host_ip == s2.host_ip) implies (s1.port != s2.port)
}

verify consistency of DeploymentPolicy
"#,
    );
    println!("已生成 {} 与 {}", cfg.display(), example.display());
    println!("下一步：policylang verify {}", example.display());
    ExitCode::Pass
}
