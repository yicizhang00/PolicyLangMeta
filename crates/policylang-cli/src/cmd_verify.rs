//! `policylang verify` —— 端到端验证（`02 §1.3` 的 ⑦ 全链路）。
//!
//! 管线：读源 → 解析 → 检查 → 生成 → 探测/路由 → 竞速 → 交叉验证 → Core 最小化
//! → 装配报告（四哈希）→ 输出（报告/SARIF/SMT/AST）→ 退出码。

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use policylang_ast::codes::*;
use policylang_ast::diag::Diagnostic;
use policylang_ast::formula::Formula;
use policylang_ast::spec::{TargetType, VerifyKind};
use policylang_check::{check, CheckOptions, CheckedSpec};
use policylang_codegen::{
    generate, CodegenOptions, CodegenOutput, EmittedQuery, EnumEncoding, ExpectedVerdict,
};
use policylang_diagnostics::{
    attribute_core, build_counterexample, minimize_core, render_fix, summary_for, template_for,
    Counterexample, FieldRange, Remediation, RuleConflictSpan, SubsetVerdict,
    VerdictFeature,
};
use policylang_governance::report::{Check, ReportInput, VerificationReport};
use policylang_governance::waiver::{self, WaiverOutcome};
use policylang_governance::{
    host_info, new_report_id, now_rfc3339, query_hash, spec_hash, stamp_compact, ExitCode,
    GateStatus,
};
use policylang_solver::{
    excluded_backends, probe_all, rebuild_script, route, solve_race, split_named_asserts,
    verify_lock, Backend, Capability, LockFile,
    Confirmation, RaceOptions, RouteOptions, Verdict,
};

use crate::exit;

/// `verify` 的全部选项（对应 `01 §4 IF-1` 的 CLI 契约）。
#[derive(Debug, Clone)]
pub struct VerifyOptions {
    pub files: Vec<PathBuf>,
    pub timeout: Duration,
    pub check: CheckOptions,
    pub output: Option<PathBuf>,
    pub sarif: Option<PathBuf>,
    pub emit_smt_dir: Option<PathBuf>,
    pub emit_ast: Option<PathBuf>,
    pub emit_capability: Option<PathBuf>,
    pub solvers: Vec<Backend>,
    pub exclude_solvers: Vec<String>,
    pub confirmation: Confirmation,
    pub minimize_core: bool,
    pub minimize_budget: usize,
    pub quiet: bool,
    pub goal_parallelism: usize,
    /// `06 §6.5.2`：`policylang.lock` 路径（`None` 表示在 CWD 自动发现）。
    pub lock_file: Option<PathBuf>,
    /// 显式禁用锁文件校验。
    pub no_lock: bool,
    /// `--allow-version-drift`：把 `E-SOLVER-VERSION` 降级为 `W-SOLVER-DRIFT`。
    pub allow_version_drift: bool,
    /// 枚举编码方式（`DD-6.2`）：`Int`（默认）或 `Datatype`（保留开关）。
    pub enum_encoding: EnumEncoding,
    /// 反例区间化（`06 §6.3.7`）：默认开启；`--no-counterexample-interval` 关闭。
    pub counterexample_interval: bool,
    /// 区间化的**总**时间预算（毫秒，默认 500）。
    pub interval_budget_ms: u64,
}

impl Default for VerifyOptions {
    fn default() -> Self {
        VerifyOptions {
            files: Vec::new(),
            timeout: Duration::from_millis(3000),
            check: CheckOptions::default(),
            output: None,
            sarif: None,
            emit_smt_dir: None,
            emit_ast: None,
            emit_capability: None,
            solvers: policylang_solver::discover_backends(),
            exclude_solvers: Vec::new(),
            confirmation: Confirmation::TwoOfN,
            minimize_core: true,
            minimize_budget: 64,
            quiet: false,
            goal_parallelism: 1,
            lock_file: None,
            no_lock: false,
            allow_version_drift: false,
            enum_encoding: EnumEncoding::default(),
            counterexample_interval: true,
            interval_budget_ms: 500,
        }
    }
}

/// 执行验证，返回退出码。
pub fn run(opts: &VerifyOptions) -> ExitCode {
    if opts.files.is_empty() {
        return exit::usage_error("verify 需要至少一个 `.plm` 文件");
    }

    // ── ① 解析（多文件按顺序合并为一次验证的检查序列）──
    let mut specs = Vec::new();
    let mut all_source = String::new();
    for f in &opts.files {
        let src = match std::fs::read_to_string(f) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("policylang: 无法读取 {}：{e}", f.display());
                return ExitCode::CompileError;
            }
        };
        all_source.push_str(&src);
        match policylang_parser::parse_spec(&src, f.to_str()) {
            Ok(s) => specs.push((f.clone(), src, s)),
            Err(diags) => return emit_compile_error(&opts.files, &all_source, &diags),
        }
    }

    let sh = spec_hash(&all_source);

    // `--emit-ast`
    if let Some(path) = &opts.emit_ast {
        let mut bundle = serde_json::Map::new();
        bundle.insert(
            "ast_schema_version".into(),
            serde_json::Value::String("1.0".into()),
        );
        let list: Vec<serde_json::Value> = specs
            .iter()
            .map(|(_, _, s)| serde_json::to_value(s).unwrap_or(serde_json::Value::Null))
            .collect();
        bundle.insert("specs".into(), serde_json::Value::Array(list));
        let txt = serde_json::Value::Object(bundle).to_string();
        if let Err(e) = std::fs::write(path, &txt) {
            eprintln!("policylang: 写入 {} 失败：{e}", path.display());
            return ExitCode::InternalError;
        }
    }

    // ── ② 检查（W1–W12）──
    let mut checks_out: Vec<Check> = Vec::new();
    let mut all_diags: Vec<Diagnostic> = Vec::new();
    let mut logic_used = String::from("QF_UF");
    let mut query_hashes: Vec<String> = Vec::new();
    let mut compile_error = false;

    for (path, _src, spec) in &specs {
        let checked = match check(spec, &opts.check) {
            Ok(c) => c,
            Err(diags) => {
                compile_error = true;
                all_diags.extend(diags.iter().cloned());
                checks_out.extend(compile_error_checks(spec, &diags));
                continue;
            }
        };
        all_diags.extend(checked.warnings.iter().cloned());

        // ── ③ 生成 ──
        let header = format!(
            "PLM-GENERATED v2.1 spec={sh} gen={}",
            policylang_governance::codegen_hash(env!("CARGO_PKG_VERSION"), "codegen-1")
        );
        let cg_opts = CodegenOptions {
            enum_encoding: opts.enum_encoding,
            ..CodegenOptions::default()
        };
        let out = match generate(&checked, &header, &cg_opts) {
            Ok(o) => o,
            Err(d) => {
                compile_error = true;
                all_diags.push(d.clone());
                checks_out.extend(compile_error_checks(spec, std::slice::from_ref(&d)));
                continue;
            }
        };
        all_diags.extend(out.warnings.iter().cloned());

        // 逻辑档位：取首个目标的档位作为报告级 `logic_used`
        if let Some(q) = out.queries.first() {
            logic_used = q.logic.clone();
        }

        // `--emit-smt`
        if let Some(dir) = &opts.emit_smt_dir {
            if let Err(e) = write_smt(dir, &out) {
                eprintln!("policylang: 写入 SMT 失败：{e}");
                return ExitCode::InternalError;
            }
        }

        // ── ④ 探测 + 路由 ──
        let mut caps = probe_all(&opts.solvers, Duration::from_millis(1200));

        // ── ④a `policylang.lock` 校验（`06 §6.5.2`，`FR-17`）──
        // 默认在**当前工作目录**自动发现 `policylang.lock`（规范的「启动时校验」）；
        // `--lock <path>` 覆盖，`--no-lock` 显式禁用。
        if !opts.no_lock {
            let lpath: Option<PathBuf> = opts.lock_file.clone().or_else(|| {
                let p = PathBuf::from("policylang.lock");
                if p.is_file() {
                    Some(p)
                } else {
                    None
                }
            });
            if let Some(lp) = lpath {
                match LockFile::read(&lp) {
                    Ok(lock) => {
                        let (drifts, ldiags) =
                            verify_lock(&lock, &caps, opts.allow_version_drift);
                        if ldiags.iter().any(|d| d.is_error()) {
                            for d in &ldiags {
                                eprintln!("{}", d.render());
                            }
                            return ExitCode::InternalError;
                        }
                        all_diags.extend(ldiags);
                        // `required = false` 且不可用者：从候选集中剔除
                        for n in excluded_backends(&drifts) {
                            caps.retain(|c| c.name != n);
                        }
                    }
                    Err(e) => {
                        eprintln!("policylang: {e}");
                        return ExitCode::InternalError;
                    }
                }
            }
        }
        if let Some(cp) = &opts.emit_capability {
            if let Err(e) = std::fs::write(cp, policylang_solver::capability_json(&caps)) {
                eprintln!("policylang: 写入能力矩阵失败：{e}");
                return ExitCode::InternalError;
            }
        }

        let results = solve_all(&out, &caps, opts, &checked);
        for r in results {
            query_hashes.push(r.query_hash.clone());
            checks_out.push(r.check);
        }
        let _ = path;
    }

    // ── ⑤ 豁免 ──
    let today = waiver::today_iso();
    let all_waivers: Vec<policylang_ast::spec::WaiverDecl> = specs
        .iter()
        .flat_map(|(_, _, s)| s.waivers.iter().cloned())
        .collect();
    let WaiverOutcome {
        entries,
        diagnostics: wdiags,
        ..
    } = waiver::apply(&mut checks_out, &all_waivers, &today);
    all_diags.extend(wdiags);

    // ── ⑥ 装配报告 ──
    let ts = now_rfc3339();
    let (host, os, arch) = host_info();
    let att = policylang_governance::AttestationRecord {
        winner_solver: checks_out
            .iter()
            .find_map(|c| c.winning_solver.clone()),
        solver_version: None,
        time_ms: checks_out.iter().map(|c| c.time_ms).sum(),
        host,
        os,
        arch,
    };
    let report = VerificationReport::build(
        ReportInput {
            report_id: new_report_id(&stamp_compact(&ts)),
            timestamp: ts,
            logic_used: logic_used.clone(),
            spec_hash: sh.clone(),
            query_hashes,
            checks: checks_out,
            waivers: entries,
            attestation: att,
        },
        compile_error,
    );

    // ── ⑦ 输出 ──
    if let Some(path) = &opts.output {
        if let Err(e) = std::fs::write(path, report.to_canonical_json()) {
            eprintln!("policylang: 写入报告失败：{e}");
            return ExitCode::InternalError;
        }
    }
    if let Some(path) = &opts.sarif {
        if let Err(e) = std::fs::write(path, policylang_governance::to_sarif(&report)) {
            eprintln!("policylang: 写入 SARIF 失败：{e}");
            return ExitCode::InternalError;
        }
    }
    // 约定：**人类可读摘要走 stdout**（可被 `--quiet` 抑制），
    // **诊断走 stderr**（错误流，便于 CI 与 `--output` 的机器消费互不干扰）。
    if !opts.quiet {
        print!("{}", report.render_text());
    }
    for d in &all_diags {
        eprintln!("{}", d.render());
    }

    match report.exit_code {
        0 => ExitCode::Pass,
        1 => ExitCode::Fail,
        2 => ExitCode::Unknown,
        3 => ExitCode::CompileError,
        _ => ExitCode::InternalError,
    }
}

/// 单个目标的求解结果。
struct GoalResult {
    check: Check,
    query_hash: String,
}

/// 求解全部目标（按 `--goal-parallelism` 有界并行）。
///
/// **进程数上界**（`C-11`）：峰值并发子进程 = `min(p, 8) × |路由后端|`（≤ `3p`），
/// **不随目标总数增长**——因为目标是**分批**消费的，每批最多 `p` 个。
fn solve_all(
    out: &CodegenOutput,
    caps: &[Capability],
    opts: &VerifyOptions,
    checked: &CheckedSpec,
) -> Vec<GoalResult> {
    // 先把「Q1+Q2」捆成一个 job，保证 `refines` 的两条查询落在同一 job
    let mut jobs: Vec<Vec<&EmittedQuery>> = Vec::new();
    let mut i = 0usize;
    while i < out.queries.len() {
        let q = &out.queries[i];
        if q.target_type == TargetType::Refines && i + 1 < out.queries.len() {
            jobs.push(vec![q, &out.queries[i + 1]]);
            i += 2;
        } else {
            jobs.push(vec![q]);
            i += 1;
        }
    }

    let p = opts.goal_parallelism.clamp(1, 8);
    let results: std::sync::Mutex<Vec<Option<GoalResult>>> =
        std::sync::Mutex::new((0..jobs.len()).map(|_| None).collect());

    if p <= 1 || jobs.len() <= 1 {
        let mut g = results.lock().unwrap();
        for (idx, j) in jobs.iter().enumerate() {
            g[idx] = Some(solve_job(j, caps, opts, checked));
        }
    } else {
        let next = std::sync::atomic::AtomicUsize::new(0);
        std::thread::scope(|scope| {
            for _ in 0..p {
                scope.spawn(|| loop {
                    let idx = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    if idx >= jobs.len() {
                        break;
                    }
                    let r = solve_job(&jobs[idx], caps, opts, checked);
                    results.lock().unwrap()[idx] = Some(r);
                });
            }
        });
    }

    results.into_inner().unwrap().into_iter().flatten().collect()
}

/// 一个 job = 一条查询（或 `refines` 的 Q1+Q2）。
fn solve_job(
    job: &[&EmittedQuery],
    caps: &[Capability],
    opts: &VerifyOptions,
    checked: &CheckedSpec,
) -> GoalResult {
    if job.len() == 2 {
        let (c, hs) = solve_refines(job[0], job[1], caps, opts, checked);
        GoalResult {
            check: c,
            query_hash: policylang_governance::aggregate_hash(&hs),
        }
    } else {
        let (c, h) = solve_one(job[0], caps, opts, checked);
        GoalResult {
            check: c,
            query_hash: h,
        }
    }
}

/// 求解单条查询并产出报告项。
fn solve_one(
    q: &EmittedQuery,
    caps: &[Capability],
    opts: &VerifyOptions,
    checked: &CheckedSpec,
) -> (Check, String) {
    let qh = query_hash(&q.canonical());
    let route_opts = RouteOptions {
        strict_logic: opts.check.strict_logic,
        only: Vec::new(),
        exclude: opts.exclude_solvers.clone(),
    };
    let r = route(&q.logic, caps, &route_opts);
    let mut diags: Vec<Diagnostic> = r.diagnostics.clone();

    // `safety` 且义务集为空（`k = 0`）⇒ 按 `06 §6.3.5` 直接判 `Pass` 并标注 `safety_vacuous`：
    // 这是**规范给定的数学事实**（`⋀∅ = ⊤`），无需查询；同时避免采信求解器对一个恒真义务的回答。
    let vacuous_safety = q.notes.iter().any(|n| n.starts_with("safety_vacuous"));
    if vacuous_safety {
        diags.push(Diagnostic::warning(
            W_SAFETY_VACUOUS,
            format!(
                "`{}` 不含除法：义务集为空，按规范直接判 `Pass` 并标注 `safety_vacuous: true`（06 §6.3.5）",
                q.goal_name
            ),
        ));
        let qh = query_hash(&q.canonical());
        let check = Check {
            check_name: q.goal_name.clone(),
            target_type: q.target_type.as_str().to_string(),
            status: GateStatus::Pass.as_str().to_string(),
            verdict: Verdict::Unsat.as_str().to_string(),
            winning_solver: None,
            time_ms: 0,
            conflicting_rules: Vec::new(),
            counterexample: None,
            verdict_feature: VerdictFeature::BoundaryValue.as_str().to_string(),
            remediation: Remediation {
                template_id: policylang_ast::diag::FixTemplateId::Fix9,
                rendered: "无需修复：义务集为空，`safety` 真空成立（safety_vacuous: true）".to_string(),
            },
            diagnostics: diags,
            core_minimized: false,
            refinement_class: None,
        };
        return (check, qh);
    }

    let no_solvers = r.is_empty();
    let race = if no_solvers {
        None
    } else {
        Some(solve_race(
            &q.canonical(),
            &r.backends,
            &RaceOptions {
                timeout: opts.timeout,
                confirmation: opts.confirmation,
            },
        ))
    };

    let (verdict, winner, time_ms, core, model, solver_errors) = match race {
        None => {
            diags.push(Diagnostic::error(
                E_SOLVER_MISSING,
                "无可路由到的求解器后端：请安装 Z3/CVC5/Bitwuzla，或用 `--solvers` 指定",
            ));
            (Verdict::Unknown, None, 0u64, Vec::new(), None, Vec::new())
        }
        Some(o) => {
            diags.extend(o.diagnostics.clone());
            let w = o.winner.clone();
            (
                o.verdict(),
                w.as_ref().map(|x| x.name.clone()),
                w.as_ref().map(|x| x.elapsed_ms).unwrap_or(0),
                w.as_ref()
                    .and_then(|x| x.raw.core().cloned())
                    .unwrap_or_default(),
                w.as_ref().and_then(|x| x.raw.model().cloned()),
                o.runs
                    .iter()
                    .filter_map(|x| x.spawn_error.clone())
                    .collect::<Vec<_>>(),
            )
        }
    };

    // 状态判定
    let pass = match q.expected {
        ExpectedVerdict::Sat => verdict == Verdict::Sat,
        ExpectedVerdict::Unsat => verdict == Verdict::Unsat,
    };
    let status = if no_solvers && verdict == Verdict::Unknown {
        // 无后端属**工具链故障**（exit 4），不是「判定不确定」
        GateStatus::Error
    } else if !verdict.is_determinate() {
        GateStatus::UnknownReviewRequired
    } else if pass {
        GateStatus::Pass
    } else {
        GateStatus::Fail
    };

    // 空真检测（06 §6.3.7）
    let vacuous = match (&q.refutation_label, status, verdict) {
        (Some(lab), GateStatus::Pass, Verdict::Unsat) => !core.iter().any(|c| c == lab),
        _ => false,
    };
    if vacuous {
        let code = match q.target_type {
            TargetType::Invariant => W_VACUOUS_INVARIANT,
            TargetType::Refines => W_VACUOUS_REFINES,
            TargetType::Safety => W_VACUOUS_SAFETY,
            _ => W_VACUOUS_SAFETY,
        };
        diags.push(Diagnostic::warning(
            code,
            format!(
                "`{}` 空真：Unsat Core 不含反证断言 `{lab}`，不可满足性完全由前提贡献；\
                 建议补跑 `verify consistency`（06 §6.3.7）",
                q.goal_name,
                lab = q.refutation_label.clone().unwrap_or_default()
            ),
        ));
    }
    for e in &solver_errors {
        diags.push(Diagnostic::error(
            E_SOLVER_MISSING,
            format!("后端启动失败：{e}"),
        ));
    }

    // Core 最小化（仅对 consistency 的 UNSAT）
    let mut core_minimized = false;
    let mut core = core;
    if status == GateStatus::Fail
        && q.target_type == TargetType::Consistency
        && opts.minimize_core
        && !core.is_empty()
        && !r.is_empty()
    {
        let (keep, named) = split_named_asserts(&q.canonical());
        let by_label: BTreeMap<String, String> = named.into_iter().collect();
        let backend = r.backends[0].clone();
        let timeout = opts.timeout;
        let res = minimize_core(core.clone(), opts.minimize_budget, |subset: &[String]| {
            let sub: Vec<(String, String)> = subset
                .iter()
                .filter_map(|l| by_label.get(l).map(|line| (l.clone(), line.clone())))
                .collect();
            let script = rebuild_script(&keep, &sub);
            let o = solve_race(
                &script,
                std::slice::from_ref(&backend),
                &RaceOptions {
                    timeout,
                    confirmation: Confirmation::None,
                },
            );
            match o.verdict() {
                Verdict::Unsat => SubsetVerdict::Unsat,
                Verdict::Sat => SubsetVerdict::Sat,
                _ => SubsetVerdict::Unknown,
            }
        });
        core_minimized = res.minimal;
        core = res.core;
        if !res.minimal {
            diags.push(Diagnostic::warning(
                W_SLOW_GOAL,
                format!(
                    "`{}` 的 Unsat Core 在预算 {} 内未达极小（已执行 {} 次重查）；\
                     报告以 `core_minimized=false` 诚实标注（06 §6.9）",
                    q.goal_name, opts.minimize_budget, res.checks
                ),
            ));
        }
    }

    // 归因与反例
    let label_index: Vec<(String, String, policylang_ast::Span)> = checked
        .labels
        .iter()
        .map(|(l, (_, owner, span))| (l.clone(), owner.clone(), *span))
        .collect();
    let conflicting: Vec<RuleConflictSpan> = if status == GateStatus::Fail
        && q.target_type == TargetType::Consistency
    {
        attribute_core(&core, &label_index)
    } else {
        Vec::new()
    };

    let counterexample: Option<Counterexample> = if status == GateStatus::Fail
        && q.target_type != TargetType::Consistency
    {
        let domains = domains_in_play(checked, q);
        let feature = classify_feature(q, status, &verdict, &core, &conflicting, &domains);
        let summary = summary_for(q.target_type.as_str(), feature, &[], None);
        let mut ce = build_counterexample(
            &checked.spec,
            &domains,
            model.as_ref().unwrap_or(&empty_map()),
            summary,
        );
        if opts.counterexample_interval {
            attach_intervals(&mut ce, q, model.as_ref().unwrap_or(&empty_map()), caps, checked, opts);
        }
        Some(ce)
    } else {
        None
    };

    let feature = classify_feature(q, status, &verdict, &core, &conflicting, &[]);
    let remediation = remediate(
        q,
        status,
        feature,
        &conflicting,
        counterexample.as_ref(),
        checked,
        opts,
        winner.as_deref(),
        &verdict,
    );

    let check = Check {
        check_name: q.goal_name.clone(),
        target_type: q.target_type.as_str().to_string(),
        status: status.as_str().to_string(),
        verdict: verdict.as_str().to_string(),
        winning_solver: winner,
        time_ms,
        conflicting_rules: conflicting,
        counterexample,
        verdict_feature: feature.as_str().to_string(),
        remediation,
        diagnostics: diags,
        core_minimized,
        refinement_class: None,
    };
    (check, qh)
}

fn empty_map() -> policylang_diagnostics::Assignment {
    BTreeMap::new()
}

/// `refines`：双查询四态分类（`06 §6.3.3`）。
fn solve_refines(
    q1: &EmittedQuery,
    q2: &EmittedQuery,
    caps: &[Capability],
    opts: &VerifyOptions,
    checked: &CheckedSpec,
) -> (Check, Vec<String>) {
    let (c1, h1) = solve_one(q1, caps, opts, checked);
    let (c2, h2) = solve_one(q2, caps, opts, checked);
    let v1 = Verdict::from_str_opt(&c1.verdict);
    let v2 = Verdict::from_str_opt(&c2.verdict);

    let (class, pass) = match (v1, v2) {
        (Some(Verdict::Unsat), Some(Verdict::Unsat)) => ("EQUIVALENT", true),
        (Some(Verdict::Unsat), Some(Verdict::Sat)) => ("STRICT", true),
        (Some(Verdict::Sat), Some(Verdict::Unsat)) => ("WIDENED", false),
        (Some(Verdict::Sat), Some(Verdict::Sat)) => ("INCOMPARABLE", false),
        _ => ("UNDETERMINED", true),
    };
    let status = if class == "UNDETERMINED" {
        GateStatus::UnknownReviewRequired
    } else if pass {
        GateStatus::Pass
    } else {
        GateStatus::Fail
    };
    let feature = match class {
        "WIDENED" => VerdictFeature::RangeWidened,
        "INCOMPARABLE" => VerdictFeature::BoundaryValue,
        _ => VerdictFeature::BoundaryValue,
    };
    let mut diags = c1.diagnostics.clone();
    diags.extend(c2.diagnostics.iter().cloned());
    // `report.schema.json` 的 `Diagnostic.code` 只允许 `^[EW]-…`，
    // 故精化分类经 `refinement_class` 字段与修复建议承载，不引入非法诊断码。
    let class_note = format!("精化分类 = {class}（Q1={} Q2={}，06 §6.3.3）", c1.verdict, c2.verdict);

    let mut check = Check {
        check_name: q1.goal_name.trim_end_matches("::Q1").to_string(),
        target_type: TargetType::Refines.as_str().to_string(),
        status: status.as_str().to_string(),
        verdict: c1.verdict.clone(),
        winning_solver: c1.winning_solver.clone().or(c2.winning_solver.clone()),
        time_ms: c1.time_ms + c2.time_ms,
        conflicting_rules: Vec::new(),
        counterexample: if status == GateStatus::Fail {
            c1.counterexample.clone()
        } else {
            None
        },
        verdict_feature: feature.as_str().to_string(),
        remediation: Remediation {
            template_id: template_for(feature),
            rendered: format!(
                "{}；{}",
                remediate(
                    q1,
                    status,
                    feature,
                    &[],
                    c1.counterexample.as_ref(),
                    checked,
                    opts,
                    c1.winning_solver.as_deref(),
                    &Verdict::from_str_opt(&c1.verdict).unwrap_or(Verdict::Unknown),
                )
                .rendered,
                class_note
            ),
        },
        diagnostics: diags,
        core_minimized: c1.core_minimized && c2.core_minimized,
        refinement_class: Some(class.to_string()),
    };
    if status != GateStatus::Fail {
        check.counterexample = None;
    }
    (check, vec![h1, h2])
}

/// 编译错误 → `Error` 级检查项（每文件一项，确保 `checks` 非空且可归因）。
fn compile_error_checks(spec: &policylang_ast::Spec, diags: &[Diagnostic]) -> Vec<Check> {
    let mut feature = VerdictFeature::NonlinearConstruct;
    for d in diags {
        match d.code.as_str() {
            E_GROUNDING_BUDGET => feature = VerdictFeature::GroundingBudgetExceeded,
            E_EMPTY_CARRIER => feature = VerdictFeature::EmptyCore,
            E_NONLINEAR | E_DIV_ZERO_CONST => feature = VerdictFeature::NonlinearConstruct,
            _ => {}
        }
    }
    // 为每个 verify 目标产生一项，保持与正常路径一致的检查粒度
    let mut out = Vec::new();
    let template = template_for(feature);
    let rendered = render_fix(
        template,
        &[(
            "expr",
            diags
                .first()
                .map(|d| d.message.as_str())
                .unwrap_or("n/a"),
        )],
    );
    if spec.verifies.is_empty() {
        out.push(Check {
            check_name: format!("<file>::compile::{}", spec.lang_version),
            target_type: "consistency".to_string(),
            status: GateStatus::Error.as_str().to_string(),
            verdict: Verdict::None.as_str().to_string(),
            winning_solver: None,
            time_ms: 0,
            conflicting_rules: Vec::new(),
            counterexample: None,
            verdict_feature: feature.as_str().to_string(),
            remediation: Remediation {
                template_id: template,
                rendered,
            },
            diagnostics: diags.to_vec(),
            core_minimized: false,
            refinement_class: None,
        });
    } else {
        for v in &spec.verifies {
            out.push(Check {
                check_name: v.kind.check_name(),
                target_type: v.kind.target_type().as_str().to_string(),
                status: GateStatus::Error.as_str().to_string(),
                verdict: Verdict::None.as_str().to_string(),
                winning_solver: None,
                time_ms: 0,
                conflicting_rules: Vec::new(),
                counterexample: None,
                verdict_feature: feature.as_str().to_string(),
                remediation: Remediation {
                    template_id: template,
                    rendered: rendered.clone(),
                },
                diagnostics: diags.to_vec(),
                core_minimized: false,
                refinement_class: None,
            });
        }
    }
    out
}

/// 反例特征分类（**确定性**：只依赖目标类型、判定、核与脚本内容）。
fn classify_feature(
    q: &EmittedQuery,
    status: GateStatus,
    verdict: &Verdict,
    core: &[String],
    conflicting: &[RuleConflictSpan],
    domains: &[String],
) -> VerdictFeature {
    if status == GateStatus::Error {
        return VerdictFeature::SolverUnavailable;
    }
    if status == GateStatus::UnknownReviewRequired {
        return if q.logic == "ALL" {
            VerdictFeature::UnknownRiskLogic
        } else {
            VerdictFeature::Timeout
        };
    }
    if core.is_empty() && status == GateStatus::Fail && q.target_type == TargetType::Consistency {
        return VerdictFeature::EmptyCore;
    }
    let _ = (verdict, domains);
    match q.target_type {
        TargetType::Consistency => VerdictFeature::ConflictingBoundPair,
        TargetType::Completeness => VerdictFeature::UncoveredRegion,
        TargetType::Mutex => VerdictFeature::MutexOverlap,
        TargetType::Safety => VerdictFeature::DenominatorZero,
        TargetType::Refines => VerdictFeature::RangeWidened,
        TargetType::Invariant => {
            if q.script.contains("bvand") || !conflicting.is_empty() {
                VerdictFeature::OutOfSubnet
            } else {
                VerdictFeature::BoundaryValue
            }
        }
    }
}

/// 生成修复建议（表驱动，`07 §7.4`）。
#[allow(clippy::too_many_arguments)]
fn remediate(
    q: &EmittedQuery,
    status: GateStatus,
    feature: VerdictFeature,
    conflicting: &[RuleConflictSpan],
    ce: Option<&Counterexample>,
    checked: &CheckedSpec,
    opts: &VerifyOptions,
    winner: Option<&str>,
    verdict: &Verdict,
) -> Remediation {
    let template = template_for(feature);
    let mut vars: Vec<(String, String)> = Vec::new();
    if conflicting.len() >= 2 {
        vars.push(("rule_a".into(), conflicting[0].rule_name.clone()));
        vars.push(("loc_a".into(), conflicting[0].loc()));
        vars.push(("rule_b".into(), conflicting[1].rule_name.clone()));
        vars.push(("loc_b".into(), conflicting[1].loc()));
    } else if let Some(c) = conflicting.first() {
        vars.push(("rule_a".into(), c.rule_name.clone()));
        vars.push(("loc_a".into(), c.loc()));
        vars.push(("rule_b".into(), c.rule_name.clone()));
        vars.push(("loc_b".into(), c.loc()));
    }
    if let Some(ce) = ce {
        if let Some(s) = ce.entity_snapshots.first() {
            vars.push(("entity".into(), s.entity.clone()));
            if let Some(f) = s.fields.first() {
                vars.push(("field".into(), f.name.clone()));
                vars.push(("value".into(), f.value.clone()));
            }
        }
        for g in &ce.globals {
            if g.value != "?" && !vars.iter().any(|(k, _)| k == &g.name) {
                vars.push((g.name.clone(), g.value.clone()));
            }
        }
        if let Some(f) = ce.entity_snapshots.first().and_then(|s| s.fields.first()) {
            vars.push(("field".into(), f.name.clone()));
            vars.push(("value".into(), f.value.clone()));
        }
    }
    vars.push(("logic".into(), q.logic.clone()));
    vars.push(("budget".into(), opts.check.max_groundings.to_string()));
    // `actual`：该目标的**实测展开规模** G(φ)（若已登记），否则退化为判定词
    let measured = checked
        .groundings
        .iter()
        .find(|(k, _)| q.goal_name.starts_with(k.as_str()))
        .map(|(_, v)| v.atoms_after);
    vars.push((
        "actual".into(),
        measured
            .map(|x| x.to_string())
            .unwrap_or_else(|| verdict.as_str().to_string()),
    ));
    vars.push(("timeout_ms".into(), opts.timeout.as_millis().to_string()));
    vars.push(("elapsed_ms".into(), "n/a".into()));
    vars.push(("solver".into(), winner.unwrap_or("n/a").to_string()));
    vars.push(("detail".into(), "探测失败或未安装".into()));
    vars.push(("solver_a".into(), winner.unwrap_or("n/a").to_string()));
    vars.push(("solver_b".into(), "n/a".into()));
    vars.push(("verdict_a".into(), verdict.as_str().to_string()));
    vars.push(("verdict_b".into(), "n/a".into()));
    vars.push(("branch_a".into(), "n/a".into()));
    vars.push(("branch_b".into(), "n/a".into()));
    vars.push((
        "expected".into(),
        match feature {
            VerdictFeature::OutOfSubnet => "规范声明的受控网段".to_string(),
            VerdictFeature::RangeWidened => "旧策略的边界".to_string(),
            VerdictFeature::UncoveredRegion => "相邻分支的覆盖区间".to_string(),
            _ => "n/a".to_string(),
        },
    ));
    vars.push(("lo".into(), "n/a".into()));
    vars.push(("hi".into(), "n/a".into()));
    vars.push((
        "expr".into(),
        "（见诊断：编译期阻断的表达式）".to_string(),
    ));

    let rendered = if status == GateStatus::Fail {
        render_fix(
            template,
            &vars.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect::<Vec<_>>(),
        )
    } else {
        // 非 FAIL：给出**中性**文本（`07 §7.4` 的修复建议只对失败有意义）
        format!(
            "无需修复：该目标判定为 {}（{}）",
            status.as_str(),
            verdict.as_str()
        )
    };
    Remediation {
        template_id: template,
        rendered,
    }
}

/// 反例区间化（`06 §6.3.7`）：为**连续排序**字段求「保持违规成立」的可自由变动区间。
///
/// ## 机制
/// 固定**其余全部已声明符号**为已得模型值（消去其它自由度），再对目标字段同时
/// `(minimize)` 与 `(maximize)`；在 `:opt.priority box` 下二者于**同一轮求解**中完成
/// ⇒ **每个字段恰好 1 次查询**（契合规范「每个 1 次查询」）。
///
/// ## 降级与预算
/// * 后端须实测支持 Optimize（`Capability::f_optimize`）；否则**静默跳过**、
///   `range` 保持 `None`（单点呈现），**不影响判定本身**（`G-4` / `G-8`）。
/// * 最多 `8` 个字段；总耗时受 `interval_budget_ms`（默认 500 ms）约束，超预算即停。
/// * 若某个已声明符号在模型中缺失，则**跳过该字段**——无法固定其余自由度时求出的
///   区间不是「该反例的区间」，给出它会误导读者。
fn attach_intervals(
    ce: &mut Counterexample,
    q: &EmittedQuery,
    model: &policylang_diagnostics::Assignment,
    caps: &[Capability],
    checked: &CheckedSpec,
    opts: &VerifyOptions,
) {
    use policylang_ast::formula::Sort;
    use policylang_ast::naming::{global_symbol, scalar_symbol};

    // 需要一个实测支持 Optimize 的可用后端
    let Some(be) = caps.iter().find(|c| c.available && c.f_optimize) else {
        return;
    };

    // 连续排序的候选（确定性顺序：全局变量 → 域声明序 → 实例升序 → 字段声明序）
    let mut cands: Vec<(String, Sort)> = Vec::new();
    for v in &checked.spec.vars {
        if matches!(v.sort, Sort::Int | Sort::Real) {
            cands.push((global_symbol(&v.name), v.sort.clone()));
        }
    }
    for d in &checked.spec.domains {
        let Some(ent) = checked.spec.find_entity(&d.entity) else {
            continue;
        };
        for i in 0..d.size as usize {
            for f in &ent.fields {
                if matches!(f.sort, Sort::Int | Sort::Real) {
                    cands.push((scalar_symbol(&d.name, i, &f.name), f.sort.clone()));
                }
            }
        }
    }
    if cands.is_empty() {
        return;
    }

    // 全部已声明符号（用于固定其余值）
    let mut all: Vec<(String, Sort)> = Vec::new();
    for v in &checked.spec.vars {
        all.push((global_symbol(&v.name), v.sort.clone()));
    }
    for d in &checked.spec.domains {
        let Some(ent) = checked.spec.find_entity(&d.entity) else {
            continue;
        };
        for i in 0..d.size as usize {
            for f in &ent.fields {
                all.push((scalar_symbol(&d.name, i, &f.name), f.sort.clone()));
            }
        }
    }

    let budget = Duration::from_millis(opts.interval_budget_ms.max(50));
    let started = Instant::now();
    let mut found: BTreeMap<String, FieldRange> = BTreeMap::new();
    let long_budget = Duration::from_millis(opts.interval_budget_ms.saturating_mul(2).max(500));

    for (sym, _sort) in cands.iter().take(8) {
        if started.elapsed() >= budget {
            break;
        }
        // 固定其余全部符号（任一缺失 ⇒ 放弃该字段，避免给出误导性的「区间」）
        let mut fixes: Vec<(String, String)> = Vec::with_capacity(all.len());
        let mut complete = true;
        for (s2, sort2) in &all {
            if s2 == sym {
                continue;
            }
            match model.get(s2) {
                Some(v) => fixes.push((s2.clone(), policylang_diagnostics::smt_literal(v, sort2))),
                None => {
                    complete = false;
                    break;
                }
            }
        }
        if !complete {
            continue;
        }
        let script = policylang_solver::build_interval_script(&q.script, &fixes, sym);
        let argv = policylang_solver::stdin_argv(&be.name, Some(long_budget));
        let r = policylang_solver::run_captured_argv(&be.path, &argv, Some(&script), long_budget);
        if r.timed_out || r.spawn_error.is_some() {
            continue;
        }
        if let Some((lo, hi)) = policylang_solver::interval_from_objectives(&r.stdout, sym) {
            found.insert(sym.clone(), FieldRange { lo, hi });
        }
    }

    if found.is_empty() {
        return;
    }

    // 回填到反例快照（符号名由域/实例/字段确定性重建）
    let mut notes: Vec<String> = Vec::new();
    for snap in &mut ce.entity_snapshots {
        for f in &mut snap.fields {
            let sym = scalar_symbol(&snap.domain, snap.internal_index, &f.name);
            if let Some(r) = found.get(&sym) {
                notes.push(format!("{} ∈ [{}, {}]", f.name, r.lo, r.hi));
                f.range = Some(r.clone());
            }
        }
    }
    for g in &mut ce.globals {
        let sym = global_symbol(&g.name);
        if let Some(r) = found.get(&sym) {
            notes.push(format!("{} ∈ [{}, {}]", g.name, r.lo, r.hi));
            g.range = Some(r.clone());
        }
    }
    if !notes.is_empty() {
        // 把区间并入摘要：读者在文本与 JSON 两处都能看到「不止一个点违规」
        notes.sort();
        notes.dedup();
        ce.summary = format!("{}（可自由变动区间：{}）", ce.summary, notes.join("，"));
    }
}

/// 该目标涉及哪些域（用于反例快照）。
fn domains_in_play(checked: &CheckedSpec, q: &EmittedQuery) -> Vec<String> {
    let policy = q.goal_name.split("::").next().unwrap_or("");
    let mut out: Vec<String> = Vec::new();
    // 出现在脚本中的域实例符号 ⇒ 反推域名（确定性：按域声明序）
    for d in &checked.spec.domains {
        let sym = policylang_ast::naming::scalar_symbol(&d.name, 0, "");
        let prefix = sym.trim_end_matches('_');
        if q.script.contains(prefix) {
            out.push(d.name.clone());
        }
    }
    let _ = policy;
    out
}

/// 写出 SMT 脚本（一目标一文件）。
fn write_smt(dir: &Path, out: &CodegenOutput) -> std::io::Result<()> {
    std::fs::create_dir_all(dir)?;
    for (i, q) in out.queries.iter().enumerate() {
        let safe: String = q
            .goal_name
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect();
        let name = format!("{:03}-{safe}.smt2", i);
        std::fs::write(dir.join(name), q.canonical())?;
    }
    Ok(())
}

/// 编译错误路径：直接输出诊断并返回 `Err`（由上层走 `Error` 报告）。
fn emit_compile_error(_files: &[PathBuf], _src: &str, diags: &[Diagnostic]) -> ExitCode {
    for d in diags {
        eprintln!("{}", d.render());
    }
    ExitCode::CompileError
}

/// 便于 `main` 复用：构造默认后端的 `Backend` 列表。
pub fn backends_from(names: &[String]) -> Vec<Backend> {
    if names.is_empty() {
        policylang_solver::discover_backends()
    } else {
        names
            .iter()
            .map(|n| {
                // `name[=path]`
                match n.split_once('=') {
                    Some((name, path)) => Backend {
                        name: name.to_string(),
                        path: path.to_string(),
                    },
                    None => Backend {
                        name: n.clone(),
                        path: n.clone(),
                    },
                }
            })
            .collect()
    }
}

/// 便于测试：不求解、仅做「解析 + 检查 + 生成」的阶段。
pub fn static_only(src: &str, opts: &CheckOptions) -> Result<(CheckedSpec, CodegenOutput), Vec<Diagnostic>> {
    let spec = policylang_parser::parse_spec(src, None)?;
    let checked = check(&spec, opts)?;
    let out = generate(&checked, "", &CodegenOptions::default())
        .map_err(|d| vec![d])?;
    Ok((checked, out))
}

/// 目标列表（供 `explain --list` 使用）。
pub fn goal_summary(spec: &policylang_ast::Spec) -> Vec<(String, String)> {
    spec.verifies
        .iter()
        .map(|v| (v.kind.check_name(), v.kind.target_type().as_str().to_string()))
        .collect()
}

/// 给定 `VerifyKind` 的公式集合（诊断/工具链复用）。
#[allow(dead_code)]
pub fn formulas_of<'a>(
    spec: &'a policylang_ast::Spec,
    kind: &VerifyKind,
) -> Vec<(&'a str, &'a Formula)> {
    match kind {
        VerifyKind::Consistency { policy } | VerifyKind::Safety { policy } => spec
            .find_policy(policy)
            .map(|p| p.rules.iter().map(|r| (r.name.as_str(), &r.formula)).collect())
            .unwrap_or_default(),
        _ => Vec::new(),
    }
}

/// 把 `Instant` 差值转毫秒。
#[allow(dead_code)]
pub fn ms_since(t: Instant) -> u64 {
    t.elapsed().as_millis() as u64
}
