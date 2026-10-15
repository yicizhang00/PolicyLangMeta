//! 求解器可执行文件的**发现**（`FR-17` 的前置步骤，服务于 `ALG-3` 能力探测）。
//!
//! `ALG-3` 只在「能真正启动后端」时才有意义，因此必须先确定后端的可执行文件位置。
//! 本模块把它做成**确定性、可配置、可离线**的三级搜索：
//!
//! 1. `PATH` 中的同名可执行文件（最高优先，尊重用户的显式环境）；
//! 2. 环境变量 [`ENV_SEARCH_PATH`]（`POLICYLANG_SOLVER_PATH`）列出的目录，**递归**查找；
//! 3. 用户级默认安装根：`~/.local/share/policylang-solvers/` 与 `~/.local/bin/`，递归查找。
//!
//! **为什么需要递归**：官方发布包的目录结构是嵌套的，例如
//! `z3/z3-5.3.0-x64-win/bin/z3.exe`、`cvc5/cvc5-Win64-x86_64-static/bin/cvc5.exe`、
//! `bitwuzla/Bitwuzla-Win64-x86_64-static/bin/bitwuzla.exe`（本项目 `scripts/install-solvers.sh`
//! 即按此布局安装）。要求用户手工把 `bin/` 逐个加进 `PATH` 既繁琐又易错。
//!
//! **为何不改 `PATH`**：修改用户级 `PATH` 是全局副作用，且在 Windows 上 `setx` 有 1024 字符
//! 截断风险。改为在**程序内**解析绝对路径，安装脚本只需解压到约定目录即可。
//!
//! 未找到时回退为**裸可执行名**（如 `"z3"`），交由 `spawn` 按 `PATH` 解析——这样「缺失」
//! 仍会以启动失败的形式暴露给 `ALG-3` 探测，从而保守禁用该后端的 `Pass` 输出（`TH-3a`）。

use std::path::{Path, PathBuf};

use crate::orchestra::Backend;
use crate::probe::DEFAULT_BACKENDS;

/// 环境变量：额外的求解器搜索根（多个路径以平台路径分隔符 `;`/`:` 分隔）。
pub const ENV_SEARCH_PATH: &str = "POLICYLANG_SOLVER_PATH";

/// 递归搜索的最大深度。
///
/// 深度 4 足以覆盖 `root/<产品>/<版本目录>/bin/<exe>`（3 层）并留一层余量，
/// 同时避免在用户目录中做无边界的深度遍历。
const MAX_DEPTH: u32 = 4;

/// 用户主目录（Windows 用 `USERPROFILE`，类 Unix 用 `HOME`）。
fn home_dir() -> Option<PathBuf> {
    std::env::var_os("USERPROFILE")
        .or_else(|| std::env::var_os("HOME"))
        .map(PathBuf::from)
}

/// 默认搜索根，**按确定性顺序**（环境变量在前，用户默认目录在后）。
pub fn default_roots() -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = Vec::new();
    if let Some(extra) = std::env::var_os(ENV_SEARCH_PATH) {
        v.extend(std::env::split_paths(&extra));
    }
    if let Some(h) = home_dir() {
        v.push(h.join(".local").join("share").join("policylang-solvers"));
        v.push(h.join(".local").join("bin"));
    }
    v
}

/// 在 `PATH` 中查找可执行文件（按 `PATH` 自身顺序，取首个命中）。
fn find_on_path(exe: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join(exe))
        .find(|c| c.is_file())
}

/// 在 `root` 下**递归**查找名为 `exe` 的文件。
///
/// 深度受限；同层子目录按名称排序后遍历，保证**确定性**（同一文件系统状态下结果唯一）。
fn find_in(root: &Path, exe: &str, depth: u32) -> Option<PathBuf> {
    if depth == 0 || !root.is_dir() {
        return None;
    }
    let mut subdirs: Vec<PathBuf> = Vec::new();
    let entries = match std::fs::read_dir(root) {
        Ok(e) => e,
        Err(_) => return None, // 无权限/已删除：静默跳过，不影响其余搜索路径
    };
    for ent in entries.flatten() {
        let p = ent.path();
        match ent.file_type() {
            Ok(ft) if ft.is_file() => {
                let hit = p
                    .file_name()
                    .and_then(|s| s.to_str())
                    .map_or(false, |n| n.eq_ignore_ascii_case(exe));
                if hit {
                    return Some(p);
                }
            }
            Ok(ft) if ft.is_dir() => subdirs.push(p),
            _ => {}
        }
    }
    subdirs.sort();
    subdirs.into_iter().find_map(|d| find_in(&d, exe, depth - 1))
}

/// 已知后端的可执行**基名**（不含平台后缀）。
pub fn base_name(name: &str) -> &str {
    DEFAULT_BACKENDS
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, b)| *b)
        .unwrap_or(name)
}

/// 解析某后端的可执行文件路径。
///
/// 命中则返回绝对路径；未命中回退为裸可执行名（由 `PATH` 在启动时解析）。
pub fn resolve(name: &str) -> String {
    let base = base_name(name);
    let exe = format!("{base}{}", std::env::consts::EXE_SUFFIX);
    find_on_path(&exe)
        .or_else(|| {
            default_roots()
                .iter()
                .find_map(|r| find_in(r, &exe, MAX_DEPTH))
        })
        .map(|p| p.to_string_lossy().into_owned())
        .unwrap_or_else(|| base.to_string())
}

/// 发现全部已知后端。
///
/// **规模与顺序恒为 [`DEFAULT_BACKENDS`]**（`z3` / `cvc5` / `bitwuzla`），
/// 与是否安装无关——保证报告的确定性与可复算性（`TH-10`）；
/// 「是否可用」由 `ALG-3` 探测回答，而非由本函数猜测。
pub fn discover() -> Vec<Backend> {
    DEFAULT_BACKENDS
        .iter()
        .map(|(name, _)| Backend {
            name: (*name).to_string(),
            path: resolve(name),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn discovery_is_deterministic_and_ordered() {
        let a = discover();
        let b = discover();
        assert_eq!(a.len(), DEFAULT_BACKENDS.len());
        assert_eq!(
            a.iter().map(|x| x.name.clone()).collect::<Vec<_>>(),
            vec!["z3", "cvc5", "bitwuzla"]
        );
        assert_eq!(a, b, "同一环境状态下发现结果必须可复算");
    }

    #[test]
    fn missing_backend_falls_back_to_bare_name() {
        // 未知名字没有可执行基名 ⇒ 回退为它自身
        assert_eq!(resolve("ghost-solver-xyz"), "ghost-solver-xyz");
        assert_eq!(base_name("ghost-solver-xyz"), "ghost-solver-xyz");
    }

    #[test]
    fn recursive_search_finds_nested_release_layout() {
        // 复刻官方发布包布局：<root>/<产品>-<版本>/bin/<exe>
        let root = std::env::temp_dir().join(format!(
            "pl-discover-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let deep = root.join("z3-9.9.9-x64-win").join("bin");
        std::fs::create_dir_all(&deep).unwrap();
        let exe = format!("probe-solver{}", std::env::consts::EXE_SUFFIX);
        std::fs::write(deep.join(&exe), b"stub").unwrap();

        let found = find_in(&root, &exe, MAX_DEPTH).expect("应能在 3 层深度内命中");
        assert_eq!(found, deep.join(&exe));

        // 超出深度上限时必须放弃（避免无边界的目录遍历）
        assert_eq!(find_in(&root, &exe, 2), None);

        // 大小写不敏感（Windows 文件系统语义）
        assert!(find_in(&root, &exe.to_uppercase(), MAX_DEPTH).is_some());

        std::fs::remove_dir_all(&root).ok();
    }

    #[test]
    fn search_is_scoped_by_file_name() {
        let root = std::env::temp_dir().join(format!(
            "pl-discover-neg-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(root.join("a").join("b")).unwrap();
        std::fs::write(root.join("a").join("b").join("other.exe"), b"x").unwrap();
        assert_eq!(find_in(&root, "wanted.exe", MAX_DEPTH), None);
        std::fs::remove_dir_all(&root).ok();
    }
}
