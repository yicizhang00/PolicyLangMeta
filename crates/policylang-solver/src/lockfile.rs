//! `policylang.lock`：求解器版本与二进制摘要的锁定（`06 §6.5.2`，`FR-17`）。
//!
//! ## 为什么必须锁定二进制
//! SMT 求解器的**版本升级会改变 `unknown` 的触发边界**，个别情况下甚至影响判定结果。
//! 审计链条（`07 §7.5` 的四哈希 + `TH-10` 可复算性）要求：给定同一 `spec_hash` 与
//! `query_hash`，任何人用**同一二进制**都能复算出同一 `proof_hash`。因此必须把
//! 「二进制 SHA-256 摘要」纳入锁定，而不只是版本号字符串。
//!
//! ## 语义（严格按 `06 §6.5.2`）
//!
//! | 情形 | 处置 |
//! |---|---|
//! | `version` 或 `binary_sha256` 不符 | `E-SOLVER-VERSION`（exit `4`） |
//! | 同上 + `--allow-version-drift` | 降级为 `W-SOLVER-DRIFT`，并在报告中记录**实际**版本 |
//! | 二进制缺失且 `required = true` | `E-SOLVER-MISSING`（exit `4`） |
//! | 二进制缺失且 `required = false` | `W-SOLVER-MISSING`，并从候选后端集**剔除** |
//!
//! ## 格式（TOML 的严格子集）
//! 为保持**逐字节确定性**（`CO-5`）且不引入 TOML 依赖，本模块自带一个**严格**的
//! 极小子集读写器：未知键、类型不符、重复段一律报错而非静默忽略——锁文件一旦被
//! 误编辑就必须立刻失败（它是审计前提，不是配置文件）。
//!
//! ```toml
//! lock_version = 1
//!
//! [[solver]]
//! name = "z3"
//! version = "5.3.0"
//! binary_sha256 = "9f2c…"
//! path = "/usr/local/bin/z3"
//! required = true
//! ```

use std::path::Path;

use policylang_ast::codes::{E_SOLVER_MISSING, E_SOLVER_VERSION, W_SOLVER_DRIFT, W_SOLVER_MISSING};
use policylang_ast::diag::Diagnostic;

use crate::probe::Capability;

/// 当前锁文件格式版本。
pub const LOCK_VERSION: u32 = 1;

/// 一个求解器的锁条目。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockEntry {
    pub name: String,
    pub version: String,
    pub binary_sha256: String,
    pub path: String,
    pub required: bool,
}

/// 锁文件。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockFile {
    pub lock_version: u32,
    pub solvers: Vec<LockEntry>,
}

/// 漂移类别。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DriftKind {
    /// 二进制缺失（`required = true` ⇒ `Error`；否则 `Warning` 并剔除）。
    Missing,
    /// 版本不符。
    VersionMismatch,
    /// 二进制摘要不符。
    HashMismatch,
}

/// 一处漂移。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Drift {
    pub name: String,
    pub kind: DriftKind,
    pub required: bool,
    pub detail: String,
}

/// 计算文件的 SHA-256（分块读取，避免把大二进制整体载入内存）。
pub fn sha256_file(path: &str) -> std::io::Result<String> {
    use sha2::{Digest, Sha256};
    use std::io::Read;

    let mut f = std::fs::File::open(path)?;
    let mut h = Sha256::new();
    let mut buf = vec![0u8; 64 * 1024];
    loop {
        let n = f.read(&mut buf)?;
        if n == 0 {
            break;
        }
        h.update(&buf[..n]);
    }
    Ok(hex::encode(h.finalize()))
}

/// 把绝对路径规范化为**可移植**形式：主目录前缀替换为 `~`。
///
/// 目的：锁文件可能被提交入库，直接写入 `C:////Users////<me>////…` 会泄露本机路径，
/// 也使文件不同机器间出现无意义差异。`path` 字段**仅作信息记录**——
/// 真正的可执行文件始终由 `discover` 解析，摘要校验针对**解析出的**文件，
/// 因此规范化不会削弱锁定的有效性（锁定的是**字节**，不是路径）。
pub fn portable_path(path: &str) -> String {
    // 两侧都先归一为 `/`：Windows 上 `USERPROFILE` 用 `\`，而 `discover` 解析出的
    // 路径用 `/`，不归一会导致前缀匹配**静默失效**（实测过）。
    let p = path.replace('\\', "/");
    for key in ["USERPROFILE", "HOME"] {
        let home = match std::env::var(key) {
            Ok(h) if !h.is_empty() => h.replace('\\', "/"),
            _ => continue,
        };
        let home = home.trim_end_matches('/');
        if home.is_empty() {
            continue;
        }
        let prefix = format!("{home}/");
        if p.len() > prefix.len() {
            if let Some(head) = p.get(..prefix.len()) {
                if head.eq_ignore_ascii_case(&prefix) {
                    return format!("~/{}", &p[prefix.len()..]);
                }
            }
        }
    }
    p
}

/// 从 `--version` 的原始输出中提取**规范化版本号**（首个 `x.y` 或 `x.y.z` 记号）。
///
/// 必要性：三款后端的 `--version` 首行格式完全不同
/// （`Z3 version 5.3.0 - 64 bit - build hashcode …`、`cvc5 1.4.2 [git …]`、`0.9.1`），
/// 直接拿整行做字符串比较会导致**每次构建都误报漂移**。
pub fn normalize_version(raw: &str) -> String {
    let first_line = raw.lines().next().unwrap_or("").trim();
    let bytes: Vec<char> = first_line.chars().collect();
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i].is_ascii_digit() {
            let start = i;
            let mut dots = 0usize;
            while i < bytes.len()
                && (bytes[i].is_ascii_digit() || (bytes[i] == '.' && dots < 2))
            {
                if bytes[i] == '.' {
                    // 必须后跟数字，否则视为该记号结束
                    if !bytes.get(i + 1).map_or(false, |c| c.is_ascii_digit()) {
                        break;
                    }
                    dots += 1;
                }
                i += 1;
            }
            let tok: String = bytes[start..i].iter().collect();
            if tok.contains('.') {
                return tok;
            }
            i = start + 1;
            continue;
        }
        i += 1;
    }
    first_line.to_string()
}

impl LockFile {
    /// 由 `ALG-3` 探测结果构造锁文件。
    ///
    /// 仅收录**可用**的后端；不可用者以空摘要登记并置 `required = false`，
    /// 以便后续在同一份锁文件上做漂移检查时能给出「缺失」而非「无此条目」。
    pub fn from_capabilities(caps: &[Capability]) -> LockFile {
        let mut solvers: Vec<LockEntry> = Vec::new();
        for c in caps {
            let sha = if c.available {
                sha256_file(&c.path).unwrap_or_default()
            } else {
                String::new()
            };
            solvers.push(LockEntry {
                name: c.name.clone(),
                version: c
                    .version
                    .as_deref()
                    .map(normalize_version)
                    .unwrap_or_default(),
                binary_sha256: sha,
                path: portable_path(&c.path),
                required: c.available,
            });
        }
        LockFile {
            lock_version: LOCK_VERSION,
            solvers,
        }
    }

    /// 渲染为确定性 TOML（字段顺序固定；未变化的内容逐字节一致）。
    pub fn render(&self) -> String {
        let mut s = String::new();
        s.push_str("# policylang.lock —— 由 `policylang lock` 生成，请勿手工编辑（06 §6.5.2）\n");
        s.push_str(&format!("lock_version = {}\n", self.lock_version));
        for e in &self.solvers {
            s.push_str("\n[[solver]]\n");
            s.push_str(&format!("name = {}\n", toml_str(&e.name)));
            s.push_str(&format!("version = {}\n", toml_str(&e.version)));
            s.push_str(&format!(
                "binary_sha256 = {}\n",
                toml_str(&e.binary_sha256)
            ));
            s.push_str(&format!("path = {}\n", toml_str(&e.path)));
            s.push_str(&format!("required = {}\n", e.required));
        }
        s
    }

    /// 解析。**严格**：未知键/段、类型不符、缺字段一律报错。
    pub fn parse(src: &str) -> Result<LockFile, String> {
        let mut lock_version: Option<u32> = None;
        let mut solvers: Vec<LockEntry> = Vec::new();
        let mut cur: Option<LockEntry> = None;
        // 每个 [[solver]] 段内已出现的键（用于重复键检测）
        let mut seen: Vec<String> = Vec::new();

        for (lineno, raw) in src.lines().enumerate() {
            let line = raw.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let err = |m: &str| format!("policylang.lock 第 {} 行：{m}", lineno + 1);

            if line == "[[solver]]" {
                if let Some(e) = cur.take() {
                    solvers.push(finish_entry(e)?);
                }
                cur = Some(LockEntry {
                    name: String::new(),
                    version: String::new(),
                    binary_sha256: String::new(),
                    path: String::new(),
                    required: false,
                });
                seen.clear();
                continue;
            }
            if line.starts_with('[') {
                return Err(err("不支持的段（仅允许 `[[solver]]`）"));
            }

            let (key, val) = line
                .split_once('=')
                .ok_or_else(|| err("不是 `key = value` 形式"))?;
            let key = key.trim();
            let val = val.trim();

            if cur.is_none() {
                if key == "lock_version" {
                    let v: u32 = val
                        .parse()
                        .map_err(|_| err("lock_version 必须是整数"))?;
                    lock_version = Some(v);
                    continue;
                }
                return Err(err(&format!("[[solver]] 之前不允许出现键 `{key}`")));
            }

            let e = cur.as_mut().unwrap();
            if seen.iter().any(|k| k == key) {
                return Err(err(&format!("键 `{key}` 重复")));
            }
            seen.push(key.to_string());

            match key {
                "name" => e.name = str_val(val).ok_or_else(|| err("name 必须是字串"))?,
                "version" => e.version = str_val(val).ok_or_else(|| err("version 必须是字串"))?,
                "binary_sha256" => {
                    e.binary_sha256 =
                        str_val(val).ok_or_else(|| err("binary_sha256 必须是字串"))?
                }
                "path" => e.path = str_val(val).ok_or_else(|| err("path 必须是字串"))?,
                "required" => {
                    e.required = match val {
                        "true" => true,
                        "false" => false,
                        _ => return Err(err("required 必须是 true/false")),
                    }
                }
                other => return Err(err(&format!("未知键 `{other}`"))),
            }
        }
        if let Some(e) = cur.take() {
            solvers.push(finish_entry(e)?);
        }

        let lv = lock_version.ok_or("policylang.lock 缺少 `lock_version`")?;
        if lv != LOCK_VERSION {
            return Err(format!(
                "policylang.lock 的 lock_version = {lv}，本版本仅支持 {LOCK_VERSION}"
            ));
        }
        Ok(LockFile {
            lock_version: lv,
            solvers,
        })
    }

    /// 读取锁文件。
    pub fn read(path: &Path) -> Result<LockFile, String> {
        let s = std::fs::read_to_string(path).map_err(|e| format!("读取 {path:?} 失败：{e}"))?;
        LockFile::parse(&s)
    }

    /// 写入锁文件（LF 行尾、末尾换行，`CO-5`）。
    pub fn write(&self, path: &Path) -> Result<(), String> {
        let body = self.render();
        let body = if body.ends_with('\n') {
            body
        } else {
            format!("{body}\n")
        };
        std::fs::write(path, body.replace("\r\n", "\n"))
            .map_err(|e| format!("写入 {path:?} 失败：{e}"))
    }
}

fn finish_entry(e: LockEntry) -> Result<LockEntry, String> {
    if e.name.is_empty() {
        return Err("[[solver]] 段缺少 `name`".to_string());
    }
    Ok(e)
}

fn toml_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn str_val(v: &str) -> Option<String> {
    let v = v.trim();
    if v.len() < 2 || !v.starts_with('"') || !v.ends_with('"') {
        return None;
    }
    let inner = &v[1..v.len() - 1];
    let mut out = String::with_capacity(inner.len());
    let mut it = inner.chars();
    while let Some(c) = it.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match it.next() {
            Some('"') => out.push('"'),
            Some('\\') => out.push('\\'),
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            _ => return None,
        }
    }
    Some(out)
}

/// 依据实测能力校验锁文件，产出漂移清单与诊断。
///
/// 返回 `(drifts, diagnostics)`；调用方据 `drifts` 过滤候选后端
/// （`required = false` 且缺失者应被剔除）。
pub fn verify_lock(
    lock: &LockFile,
    caps: &[Capability],
    allow_drift: bool,
) -> (Vec<Drift>, Vec<Diagnostic>) {
    let mut drifts: Vec<Drift> = Vec::new();
    let mut diags: Vec<Diagnostic> = Vec::new();

    for ent in &lock.solvers {
        let cap = caps.iter().find(|c| c.name == ent.name);

        // ① 缺失
        let missing = match cap {
            None => true,
            Some(c) => !c.available,
        };
        if missing {
            if ent.required {
                diags.push(Diagnostic::error(
                    E_SOLVER_MISSING,
                    format!(
                        "锁文件要求后端 `{}`（required = true），但它不可用（06 §6.5.2）",
                        ent.name
                    ),
                ));
            } else {
                diags.push(Diagnostic::warning(
                    W_SOLVER_MISSING,
                    format!(
                        "锁文件中的后端 `{}` 不可用（required = false）：从候选中剔除（06 §6.5.2）",
                        ent.name
                    ),
                ));
            }
            drifts.push(Drift {
                name: ent.name.clone(),
                kind: DriftKind::Missing,
                required: ent.required,
                detail: "二进制不可用".into(),
            });
            continue;
        }

        let cap = cap.expect("已判定非缺失");

        // ② 版本
        let actual_ver = cap
            .version
            .as_deref()
            .map(normalize_version)
            .unwrap_or_default();
        if !ent.version.is_empty() && actual_ver != ent.version {
            let detail = format!("锁定 {} ⇒ 实际 {}", ent.version, actual_ver);
            if allow_drift {
                diags.push(Diagnostic::warning(
                    W_SOLVER_DRIFT,
                    format!("后端 `{}` 版本漂移（已允许）：{detail}（06 §6.5.2）", ent.name),
                ));
            } else {
                diags.push(Diagnostic::error(
                    E_SOLVER_VERSION,
                    format!(
                        "后端 `{}` 版本不符：{detail}；如需继续请加 `--allow-version-drift`（06 §6.5.2）",
                        ent.name
                    ),
                ));
            }
            drifts.push(Drift {
                name: ent.name.clone(),
                kind: DriftKind::VersionMismatch,
                required: ent.required,
                detail,
            });
        }

        // ③ 二进制摘要
        if !ent.binary_sha256.is_empty() {
            match sha256_file(&cap.path) {
                Ok(actual) => {
                    if actual != ent.binary_sha256 {
                        let detail = format!(
                            "锁定 {}… ⇒ 实际 {}…",
                            &ent.binary_sha256[..8.min(ent.binary_sha256.len())],
                            &actual[..8.min(actual.len())]
                        );
                        if allow_drift {
                            diags.push(Diagnostic::warning(
                                W_SOLVER_DRIFT,
                                format!(
                                    "后端 `{}` 二进制摘要漂移（已允许）：{detail}（06 §6.5.2）",
                                    ent.name
                                ),
                            ));
                        } else {
                            diags.push(Diagnostic::error(
                                E_SOLVER_VERSION,
                                format!(
                                    "后端 `{}` 二进制摘要不符：{detail}；如需继续请加 `--allow-version-drift`（06 §6.5.2）",
                                    ent.name
                                ),
                            ));
                        }
                        drifts.push(Drift {
                            name: ent.name.clone(),
                            kind: DriftKind::HashMismatch,
                            required: ent.required,
                            detail,
                        });
                    }
                }
                Err(e) => {
                    diags.push(Diagnostic::warning(
                        W_SOLVER_DRIFT,
                        format!("无法读取后端 `{}` 的二进制以校验摘要：{e}", ent.name),
                    ));
                }
            }
        }
    }
    (drifts, diags)
}

/// 漂移是否**阻断**（存在 `Error` 级诊断）。
pub fn is_blocking(diags: &[Diagnostic]) -> bool {
    diags.iter().any(|d| d.is_error())
}

/// 应被剔除的后端名（`required = false` 且不可用）。
pub fn excluded_backends(drifts: &[Drift]) -> Vec<String> {
    drifts
        .iter()
        .filter(|d| d.kind == DriftKind::Missing && !d.required)
        .map(|d| d.name.clone())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cap(name: &str, ver: &str, path: &str, available: bool) -> Capability {
        Capability {
            name: name.into(),
            path: path.into(),
            version: Some(ver.into()),
            available,
            logics: Default::default(),
            f_model: false,
            f_unsat_core: false,
            f_incremental: false,
            f_div_mod: false,
            f_regex_inter: false,
            f_proof: false,
            f_optimize: false,
            notes: vec![],
        }
    }

    #[test]
    fn round_trip_is_byte_deterministic() {
        let lock = LockFile {
            lock_version: 1,
            solvers: vec![
                LockEntry {
                    name: "z3".into(),
                    version: "5.3.0".into(),
                    binary_sha256: "abc123".into(),
                    path: "C:/s/z3.exe".into(),
                    required: true,
                },
                LockEntry {
                    name: "cvc5".into(),
                    version: "1.4.2".into(),
                    binary_sha256: "def456".into(),
                    path: "C:/s/cvc5.exe".into(),
                    required: false,
                },
            ],
        };
        let s = lock.render();
        assert_eq!(s, lock.render(), "渲染必须逐字节可复算");
        assert!(s.contains("[[solver]]"));
        assert_eq!(LockFile::parse(&s).unwrap(), lock);
    }

    #[test]
    fn parse_rejects_unknown_key_and_bad_type() {
        let bad = "lock_version = 1\n[[solver]]\nname = \"z3\"\nversion = 1.2.3\n";
        let e = LockFile::parse(bad).unwrap_err();
        assert!(e.contains("version 必须是字串"), "{e}");

        let bad2 = "lock_version = 1\n[[solver]]\nname = \"z3\"\nbogus = \"x\"\n";
        let e2 = LockFile::parse(bad2).unwrap_err();
        assert!(e2.contains("未知键"), "{e2}");

        let bad3 = "lock_version = 2\n";
        assert!(LockFile::parse(bad3).unwrap_err().contains("lock_version"));
    }

    #[test]
    fn parse_rejects_key_before_first_section() {
        let s = "lock_version = 1\nname = \"z3\"\n";
        assert!(LockFile::parse(s).unwrap_err().contains("之前不允许"));
    }

    #[test]
    fn portable_path_hides_home_directory_with_mixed_separators() {
        // 无主目录前缀时只做分隔符归一
        assert_eq!(portable_path("z3"), "z3");
        assert_eq!(portable_path(r"C:\other\z3.exe"), "C:/other/z3.exe");
        assert_eq!(portable_path("/usr/local/bin/z3"), "/usr/local/bin/z3");

        let home = match std::env::var("USERPROFILE").or_else(|_| std::env::var("HOME")) {
            Ok(h) if !h.is_empty() => h,
            _ => return, // 无主目录环境：跳过
        };
        let home_fwd = home.replace('\\', "/");

        // 三种写法都必须被识别（曾因只处理反斜杠而与真实路径不匹配）
        for p in [
            format!("{home}/x/y/z3.exe"),       // 全正斜杠（`discover` 的真实形态）
            format!("{home}\\x\\y\\z3.exe"), // 全反斜杠
            format!("{home_fwd}/x/y/z3.exe"),   // 混合
        ] {
            let got = portable_path(&p);
            assert_eq!(got, "~/x/y/z3.exe", "输入 {p} 应被规范化");
            assert!(!got.contains(&home_fwd), "不得泄露绝对主目录：{got}");
        }
    }

    #[test]
    fn version_normalization_handles_all_three_backends() {
        // 实测的三种 `--version` 首行格式
        assert_eq!(
            normalize_version("Z3 version 5.3.0 - 64 bit - build hashcode 2e8d6ed804"),
            "5.3.0"
        );
        assert_eq!(normalize_version("cvc5 1.4.2 [git 282d5e0 on branch HEAD]"), "1.4.2");
        assert_eq!(normalize_version("0.9.1"), "0.9.1");
        // 无版本记号时回退首行
        assert_eq!(normalize_version("mystery solver"), "mystery solver");
    }

    #[test]
    fn missing_required_is_blocking_but_optional_is_not() {
        let req = LockFile {
            lock_version: 1,
            solvers: vec![LockEntry {
                name: "z3".into(),
                version: "5.3.0".into(),
                binary_sha256: String::new(),
                path: "z3".into(),
                required: true,
            }],
        };
        let caps = vec![cap("z3", "", "z3", false)];
        let (drifts, diags) = verify_lock(&req, &caps, false);
        assert!(is_blocking(&diags), "required 缺失必须阻断");
        assert_eq!(drifts[0].kind, DriftKind::Missing);

        let opt = LockFile {
            lock_version: 1,
            solvers: vec![LockEntry {
                required: false,
                ..req.solvers[0].clone()
            }],
        };
        let (drifts2, diags2) = verify_lock(&opt, &caps, false);
        assert!(!is_blocking(&diags2), "可选缺失不应阻断");
        assert_eq!(excluded_backends(&drifts2), vec!["z3".to_string()]);
    }

    #[test]
    fn version_drift_downgrades_with_flag() {
        let lock = LockFile {
            lock_version: 1,
            solvers: vec![LockEntry {
                name: "z3".into(),
                version: "4.13.0".into(),
                binary_sha256: String::new(),
                path: "z3".into(),
                required: true,
            }],
        };
        let caps = vec![cap("z3", "Z3 version 5.3.0 - 64 bit", "z3", true)];

        let (_, strict) = verify_lock(&lock, &caps, false);
        assert!(is_blocking(&strict));

        let (_, lax) = verify_lock(&lock, &caps, true);
        assert!(!is_blocking(&lax), "允许漂移时不得阻断");
        assert!(lax.iter().any(|d| d.code == W_SOLVER_DRIFT));
    }

    #[test]
    fn hash_mismatch_is_detected_against_real_file() {
        // 用一个真实存在的临时文件做摘要校验
        let p = std::env::temp_dir().join(format!("pl-lock-{}", std::process::id()));
        std::fs::write(&p, b"policylang").unwrap();
        let real = sha256_file(p.to_str().unwrap()).unwrap();
        assert_eq!(real.len(), 64);

        let lock = LockFile {
            lock_version: 1,
            solvers: vec![LockEntry {
                name: "z3".into(),
                version: "5.3.0".into(),
                binary_sha256: "00".repeat(32), // 故意错误
                path: p.to_string_lossy().into_owned(),
                required: true,
            }],
        };
        let caps = vec![cap("z3", "Z3 version 5.3.0", p.to_str().unwrap(), true)];
        let (drifts, diags) = verify_lock(&lock, &caps, false);
        assert!(is_blocking(&diags));
        assert_eq!(drifts[0].kind, DriftKind::HashMismatch);

        // 正确摘要则无漂移
        let ok = LockFile {
            lock_version: 1,
            solvers: vec![LockEntry {
                binary_sha256: real,
                ..lock.solvers[0].clone()
            }],
        };
        let (d2, g2) = verify_lock(&ok, &caps, false);
        assert!(d2.is_empty() && g2.is_empty(), "{d2:?} {g2:?}");

        std::fs::remove_file(&p).ok();
    }
}
