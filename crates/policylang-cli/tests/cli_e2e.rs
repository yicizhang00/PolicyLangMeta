//! 端到端集成测试（`10 §10.2` 的 `AC` 家族 + `07 §7.7` 的五分支门禁）。
//!
//! 说明：本环境未安装 Z3/CVC5/Bitwuzla，故通过 `--solvers stub=<桩求解器路径>` 挂载
//! `pl-stub-solver`（测试替身）以覆盖完整管线；「无求解器」路径亦单独覆盖（`E-SOLVER-MISSING`）。

use std::path::{Path, PathBuf};
use std::process::Command;

fn exe(name: &str) -> PathBuf {
    match name {
        "policylang" => PathBuf::from(env!("CARGO_BIN_EXE_policylang")),
        _ => PathBuf::from(env!("CARGO_BIN_EXE_pl-stub-solver")),
    }
}

#[derive(Debug)]
struct Out {
    code: i32,
    stdout: String,
    stderr: String,
}

fn run(args: &[&str], verdict: &str, env_extra: &[(&str, &str)]) -> Out {
    let mut c = Command::new(exe("policylang"));
    c.args(args);
    c.env("PL_STUB_VERDICT", verdict);
    for (k, v) in env_extra {
        c.env(k, v);
    }
    let o = c.output().expect("应能启动 policylang");
    Out {
        code: o.status.code().unwrap_or(-1),
        stdout: String::from_utf8_lossy(&o.stdout).to_string(),
        stderr: String::from_utf8_lossy(&o.stderr).to_string(),
    }
}

fn stub_arg() -> String {
    format!("stub={}", exe("pl-stub-solver").display())
}

fn tmp_dir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("pl-e2e-{}-{}", tag, std::process::id()));
    let _ = std::fs::create_dir_all(&d);
    d
}

fn write(dir: &Path, name: &str, body: &str) -> PathBuf {
    let p = dir.join(name);
    std::fs::write(&p, body).expect("写入测试规范");
    p
}

const CONSISTENCY_OK: &str = r##"#lang policylang 2
entity E { a: Int [min: 1, max: 3] }
domain D: Set[E] [size: 2]
policy P { rule R: forall s in D: s.a >= 1 }
verify consistency of P
"##;

#[test]
fn version_and_help_exit_zero() {
    assert_eq!(run(&["version"], "sat", &[]).code, 0);
    assert_eq!(run(&["help"], "sat", &[]).code, 0);
    assert_eq!(run(&[], "sat", &[]).code, 4); // 无子命令 ⇒ 内部错误
    assert_eq!(run(&["nope"], "sat", &[]).code, 4);
}

#[test]
fn check_is_static_only_and_reports_logics() {
    let d = tmp_dir("check");
    let f = write(&d, "a.plm", CONSISTENCY_OK);
    let o = run(&["check", f.to_str().unwrap()], "sat", &[]);
    assert_eq!(o.code, 0, "{o:?}");
    assert!(o.stdout.contains("逻辑"), "{}", o.stdout);
    assert!(o.stdout.contains("QF_LIA"), "{}", o.stdout);
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn compile_error_yields_exit_3_and_error_report() {
    let d = tmp_dir("compile");
    // 非线性：`a * b` 两侧皆非常量（C-5 / AC-4）
    let f = write(
        &d,
        "bad.plm",
        "#lang policylang 2\nentity E { a: Int, b: Int }\ndomain D: Set[E] [size: 2]\n\
         policy P { rule R: forall s in D: s.a * s.b > 1 }\nverify consistency of P\n",
    );
    let rep = d.join("r.json");
    let o = run(
        &[
            "verify",
            f.to_str().unwrap(),
            "--output",
            rep.to_str().unwrap(),
            "--solvers",
            &stub_arg(),
        ],
        "sat",
        &[],
    );
    assert_eq!(o.code, 3, "编译错误应退出 3；stderr={}", o.stderr);
    assert!(o.stderr.contains("E-NONLINEAR"), "{}", o.stderr);
    // 报告存在且为 Error 级
    let r: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&rep).unwrap()).expect("报告必须是合法 JSON");
    assert_eq!(r["overall_status"], "Error");
    assert_eq!(r["exit_code"], 3);
    assert_eq!(r["checks"][0]["status"], "Error");
    assert_eq!(r["checks"][0]["verdict"], "none");
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn missing_header_is_compile_error() {
    let d = tmp_dir("hdr");
    let f = write(&d, "nohdr.plm", "entity E { a: Int }\n");
    let o = run(&["check", f.to_str().unwrap()], "sat", &[]);
    assert_eq!(o.code, 3);
    assert!(o.stderr.contains("E-BAD-HEADER"), "{}", o.stderr);
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn pass_path_exits_zero_and_writes_valid_report() {
    let d = tmp_dir("pass");
    let f = write(&d, "a.plm", CONSISTENCY_OK);
    let rep = d.join("r.json");
    let sarif = d.join("r.sarif");
    let smt = d.join("smt");
    let o = run(
        &[
            "verify",
            f.to_str().unwrap(),
            "--output",
            rep.to_str().unwrap(),
            "--sarif",
            sarif.to_str().unwrap(),
            "--emit-smt",
            smt.to_str().unwrap(),
            "--solvers",
            &stub_arg(),
        ],
        "sat",
        &[],
    );
    assert_eq!(o.code, 0, "stdout={} stderr={}", o.stdout, o.stderr);

    let r: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&rep).unwrap()).expect("报告必须是合法 JSON");
    assert_eq!(r["overall_status"], "Pass");
    assert_eq!(r["exit_code"], 0);
    assert_eq!(r["schema_version"], "1.0");
    assert_eq!(r["checks"][0]["target_type"], "consistency");
    assert_eq!(r["checks"][0]["status"], "Pass");
    assert_eq!(r["summary"]["total"], 1);
    assert_eq!(r["summary"]["pass"], 1);
    // 四哈希齐备且格式正确
    for k in ["spec_hash", "query_hash", "proof_hash", "attestation_hash"] {
        let h = r[k].as_str().unwrap();
        assert_eq!(h.len(), 64, "{k} 应为 64 位 hex");
        assert!(h.chars().all(|c| c.is_ascii_hexdigit()));
    }
    // SMT 脚本已导出且不含量词（INV-G）
    let entries: Vec<_> = std::fs::read_dir(&smt).unwrap().flatten().collect();
    assert!(!entries.is_empty());
    let txt = std::fs::read_to_string(entries[0].path()).unwrap();
    assert!(!txt.contains("(forall"));
    assert!(txt.contains("(set-logic QF_LIA)"));

    // SARIF 可解析
    let s: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&sarif).unwrap()).expect("SARIF 必须是合法 JSON");
    assert_eq!(s["version"], "2.1.0");
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn unsat_consistency_yields_fail_with_minimized_core() {
    let d = tmp_dir("fail");
    let f = write(
        &d,
        "conflict.plm",
        "#lang policylang 2\nvar x: Int [min: 0, max: 100]\n\
         policy P { rule High: x > 80\n rule Low: x < 20 }\nverify consistency of P\n",
    );
    let rep = d.join("r.json");
    let o = run(
        &[
            "verify",
            f.to_str().unwrap(),
            "--output",
            rep.to_str().unwrap(),
            "--no-minimize-core",
            "--solvers",
            &stub_arg(),
        ],
        "unsat",
        &[],
    );
    assert_eq!(o.code, 1, "UNSAT 的 consistency 应判 Fail ⇒ exit 1；stdout={}", o.stdout);
    let r: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&rep).unwrap()).unwrap();
    assert_eq!(r["overall_status"], "Fail");
    assert_eq!(r["exit_code"], 1);
    assert_eq!(r["checks"][0]["verdict"], "unsat");
    // consistency 的 FAIL 必须带冲突核、且反例为 null（schema allOf）
    let core = r["checks"][0]["conflicting_rules"].as_array().unwrap();
    assert!(!core.is_empty(), "应归因到冲突规则");
    assert!(r["checks"][0]["counterexample"].is_null());
    // 归因到 DSL 规则名
    let names: Vec<&str> = core.iter().filter_map(|c| c["rule_name"].as_str()).collect();
    assert!(names.contains(&"High") || names.contains(&"Low"), "{names:?}");
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn sat_invariant_yields_fail_with_counterexample_and_primary_key() {
    let d = tmp_dir("inv");
    let f = write(
        &d,
        "inv.plm",
        "#lang policylang 2\nentity Service { @key id: Int [min: 1, max: 9], ip: IPv4 }\n\
         domain Services: Set[Service] [size: 2]\n\
         policy P { rule R: forall s in Services: s.ip == s.ip }\n\
         invariant I { forall s in Services: in_cidr(s.ip, \"10.0.0.0/8\") }\n\
         verify invariant I under P\n",
    );
    let rep = d.join("r.json");
    let o = run(
        &[
            "verify",
            f.to_str().unwrap(),
            "--output",
            rep.to_str().unwrap(),
            "--solvers",
            &stub_arg(),
        ],
        "sat",
        &[],
    );
    assert_eq!(o.code, 1, "invariant 的 SAT 应判 Fail ⇒ exit 1；stdout={}", o.stdout);
    let r: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&rep).unwrap()).unwrap();
    let ce = &r["checks"][0]["counterexample"];
    assert!(!ce.is_null(), "invariant 的 FAIL 必须给出反例");
    let snaps = ce["entity_snapshots"].as_array().unwrap();
    assert_eq!(snaps.len(), 2, "应给出 2 个实例快照");
    // display_index 从 1 起；@key 主键被还原
    assert_eq!(snaps[0]["display_index"], 1);
    assert_eq!(snaps[1]["display_index"], 2);
    assert_eq!(snaps[0]["primary_key"]["field"], "id");
    // IPv4 反例为点分十进制
    let ip = snaps[0]["fields"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["name"] == "ip")
        .unwrap()["value"]
        .as_str()
        .unwrap();
    assert_eq!(ip.matches('.').count(), 3, "IPv4 应还原为点分十进制：{ip}");
    assert_eq!(r["checks"][0]["verdict"], "sat");
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn unknown_yields_exit_2_and_honest_status() {
    let d = tmp_dir("unknown");
    let f = write(&d, "a.plm", CONSISTENCY_OK);
    let rep = d.join("r.json");
    let o = run(
        &[
            "verify",
            f.to_str().unwrap(),
            "--output",
            rep.to_str().unwrap(),
            "--solvers",
            &stub_arg(),
        ],
        "unknown",
        &[],
    );
    assert_eq!(o.code, 2, "UNKNOWN 必须转人工 ⇒ exit 2（G-8 诚实阻断）");
    let r: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&rep).unwrap()).unwrap();
    assert_eq!(r["overall_status"], "UnknownReviewRequired");
    assert_eq!(r["checks"][0]["status"], "UnknownReviewRequired");
    // 绝不坍塌为 Pass
    assert_ne!(r["checks"][0]["status"], "Pass");
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn no_solver_available_is_internal_error_not_pass() {
    let d = tmp_dir("nosolver");
    let f = write(&d, "a.plm", CONSISTENCY_OK);
    let rep = d.join("r.json");
    // 指向一个不存在的后端 ⇒ E-SOLVER-MISSING ⇒ exit 4（B-13）
    let o = run(
        &[
            "verify",
            f.to_str().unwrap(),
            "--output",
            rep.to_str().unwrap(),
            "--solvers",
            "ghost=definitely-not-a-real-binary-xyz",
        ],
        "sat",
        &[],
    );
    assert_eq!(o.code, 4, "求解器缺失属内部错误 ⇒ exit 4；stdout={}", o.stdout);
    let r: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&rep).unwrap()).unwrap();
    assert_eq!(r["overall_status"], "Error");
    assert_eq!(r["exit_code"], 4);
    let codes: Vec<&str> = r["checks"][0]["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|d| d["code"].as_str())
        .collect();
    assert!(codes.contains(&"E-SOLVER-MISSING"), "{codes:?}");
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn timeout_yields_unknown_not_pass() {
    let d = tmp_dir("timeout");
    let f = write(&d, "a.plm", CONSISTENCY_OK);
    // 桩求解器延时 400ms > --timeout 50ms ⇒ 超时 ⇒ UnknownReviewRequired（AC-6）
    let o = run(
        &[
            "verify",
            f.to_str().unwrap(),
            "--timeout",
            "50",
            "--solvers",
            &stub_arg(),
        ],
        "sat",
        &[("PL_STUB_DELAY_MS", "400")],
    );
    assert_eq!(o.code, 2, "超时必须转人工 ⇒ exit 2；stdout={}", o.stdout);
    assert!(o.stdout.contains("UnknownReviewRequired"), "{}", o.stdout);
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn waiver_converts_fail_to_waived_and_exit_zero() {
    let d = tmp_dir("waiver");
    let f = write(
        &d,
        "w.plm",
        "#lang policylang 2\nvar x: Int [min: 0, max: 10]\n\
         policy P { rule High: x > 8\n rule Low: x < 2 }\n\
         waiver W { target: P\n owner: \"alice\"\n approver: \"bob\"\n expires: \"2099-12-31\"\n reason: \"migration\" }\n\
         verify consistency of P\n",
    );
    let rep = d.join("r.json");
    let o = run(
        &[
            "verify",
            f.to_str().unwrap(),
            "--output",
            rep.to_str().unwrap(),
            "--no-minimize-core",
            "--solvers",
            &stub_arg(),
        ],
        "unsat",
        &[],
    );
    assert_eq!(o.code, 0, "生效豁免应把 Fail 覆盖为 Waived ⇒ exit 0；stdout={}", o.stdout);
    let r: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&rep).unwrap()).unwrap();
    assert_eq!(r["overall_status"], "Waived");
    assert_eq!(r["checks"][0]["status"], "Waived");
    assert_eq!(r["waivers"][0]["state"], "Active");
    assert_eq!(r["summary"]["waived"], 1);
    assert_eq!(r["summary"]["fail"], 0);
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn expired_waiver_falls_back_to_fail() {
    let d = tmp_dir("wail");
    let f = write(
        &d,
        "w.plm",
        "#lang policylang 2\nvar x: Int [min: 0, max: 10]\n\
         policy P { rule High: x > 8\n rule Low: x < 2 }\n\
         waiver W { target: P\n owner: \"alice\"\n approver: \"bob\"\n expires: \"2000-01-01\"\n reason: \"stale\" }\n\
         verify consistency of P\n",
    );
    let rep = d.join("r.json");
    let o = run(
        &[
            "verify",
            f.to_str().unwrap(),
            "--output",
            rep.to_str().unwrap(),
            "--no-minimize-core",
            "--solvers",
            &stub_arg(),
        ],
        "unsat",
        &[],
    );
    assert_eq!(o.code, 1, "过期豁免必须回退 Fail ⇒ exit 1");
    let r: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&rep).unwrap()).unwrap();
    assert_eq!(r["checks"][0]["status"], "Fail");
    assert_eq!(r["waivers"][0]["state"], "Expired");
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn refines_four_state_classification() {
    let d = tmp_dir("refines");
    let f = write(
        &d,
        "r.plm",
        "#lang policylang 2\nvar p: Int [min: 0, max: 65535]\n\
         policy Old { rule R: p in [1024..65535] }\n\
         policy New { rule R: p in [80..65535] }\n\
         verify New refines Old\n",
    );
    let rep = d.join("r.json");
    // 桩求解器恒 sat ⇒ Q1=sat, Q2=sat ⇒ INCOMPARABLE / Fail
    let o = run(
        &[
            "verify",
            f.to_str().unwrap(),
            "--output",
            rep.to_str().unwrap(),
            "--solvers",
            &stub_arg(),
        ],
        "sat",
        &[],
    );
    assert_eq!(o.code, 1);
    let r: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&rep).unwrap()).unwrap();
    assert_eq!(r["checks"][0]["target_type"], "refines");
    assert_eq!(r["checks"][0]["refinement_class"], "INCOMPARABLE");
    // 两条查询 ⇒ 记录两条查询哈希的聚合
    assert_eq!(r["query_hash"].as_str().unwrap().len(), 64);
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn all_three_shipped_examples_verify_without_panic() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    for name in [
        "cloud-deployment.plm",
        "exchange-compliance.plm",
        "marketing-coupon.plm",
    ] {
        let p = root.join("examples").join(name);
        let rep = std::env::temp_dir().join(format!("pl-{name}.json"));
        let o = run(
            &[
                "verify",
                p.to_str().unwrap(),
                "--output",
                rep.to_str().unwrap(),
                "--solvers",
                &stub_arg(),
            ],
            "sat",
            &[],
        );
        // 允许 0/1/2（不同示例的目标期望不同），但**不得**出现内部错误或 panic
        assert!(
            (0..=2).contains(&o.code),
            "{name} 出现非预期退出码 {}：stdout={} stderr={}",
            o.code,
            o.stdout,
            o.stderr
        );
        assert!(!o.stderr.contains("panicked"), "{name} 发生 panic：{}", o.stderr);
        let r: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(&rep).unwrap()).unwrap();
        assert_eq!(r["schema_version"], "1.0");
        assert!(r["summary"]["total"].as_u64().unwrap() >= 1);
        let _ = std::fs::remove_file(&rep);
    }
}

#[test]
fn solvers_subcommand_lists_backends() {
    let o = run(&["solvers"], "sat", &[]);
    assert_eq!(o.code, 0);
    for n in ["z3", "cvc5", "bitwuzla"] {
        assert!(o.stdout.contains(n), "{}", o.stdout);
    }
}

#[test]
fn explain_lists_and_prints_goal() {
    let d = tmp_dir("explain");
    let f = write(&d, "a.plm", CONSISTENCY_OK);
    let l = run(&["explain", "--list", f.to_str().unwrap()], "sat", &[]);
    assert_eq!(l.code, 0);
    assert!(l.stdout.contains("consistency"), "{}", l.stdout);
    let e = run(
        &["explain", "--goal", "consistency", f.to_str().unwrap()],
        "sat",
        &[],
    );
    assert_eq!(e.code, 0);
    assert!(e.stdout.contains("(set-logic QF_LIA)"), "{}", e.stdout);
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn init_scaffolds_parseable_project() {
    let d = tmp_dir("init");
    let o = run(&["init", d.to_str().unwrap()], "sat", &[]);
    assert_eq!(o.code, 0, "{}", o.stderr);
    assert!(d.join("policylang.toml").is_file());
    let ex = d.join("example.plm");
    assert!(ex.is_file());
    // 生成的示例必须可通过 check
    let c = run(&["check", ex.to_str().unwrap()], "sat", &[]);
    assert_eq!(c.code, 0, "{}", c.stderr);
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn fmt_normalizes_and_is_idempotent() {
    let d = tmp_dir("fmt");
    let f = write(
        &d,
        "b.plm",
        "\u{feff}#lang policylang 2\r\nentity E { a: Int }\r\n",
    );
    let o = run(&["fmt", "--write", f.to_str().unwrap()], "sat", &[]);
    assert_eq!(o.code, 0, "{}", o.stderr);
    let t = std::fs::read_to_string(&f).unwrap();
    assert!(!t.starts_with('\u{feff}'));
    assert!(!t.contains('\r'));
    assert!(t.ends_with('\n'));
    // 幂等
    let o2 = run(&["fmt", "--write", f.to_str().unwrap()], "sat", &[]);
    assert_eq!(o2.code, 0);
    assert_eq!(std::fs::read_to_string(&f).unwrap(), t);
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn diff_subcommand_reports_refinement() {
    let d = tmp_dir("diff");
    let f = write(
        &d,
        "r.plm",
        "#lang policylang 2\nvar p: Int [min: 0, max: 65535]\n\
         policy Old { rule R: p in [1024..65535] }\n\
         policy New { rule R: p in [80..65535] }\n",
    );
    let o = run(
        &[
            "diff",
            "--new",
            "New",
            "--old",
            "Old",
            f.to_str().unwrap(),
            "--solvers",
            &stub_arg(),
        ],
        "unsat",
        &[],
    );
    // Q1=unsat Q2=unsat ⇒ EQUIVALENT ⇒ Pass ⇒ 0
    assert_eq!(o.code, 0, "stdout={} stderr={}", o.stdout, o.stderr);
    assert!(o.stdout.contains("EQUIVALENT"), "{}", o.stdout);
    let _ = std::fs::remove_dir_all(&d);
}
