//! 展平命名与 `:named` 标签生成 —— **单一实现**（`INV-L2`，`03 §3.2.4`、`06 §6.1.4 NM-1…NM-4`）。
//!
//! 声明发射器（`codegen`）与 `ground` 必须复用本模块的函数，杜绝双处漂移（修正 `A-7`）。
//!
//! ## 关于 `escape()` 的**单射性修正**（实现说明）
//!
//! `06 §6.1.4 NM-4` 原文为「非 `[A-Za-z0-9_]` 字符替换为 `_u` + 4 位十六进制」，即**保留下划线**。
//! 但该规则**不是单射**的，反例：
//!
//! ```text
//! escape("-")      = "_u002D"
//! escape("_u002D") = "_u002D"    // 下划线被保留 ⇒ 与上一行碰撞
//! ```
//!
//! 这与 `A-7` 要求「命名编码必须单射」直接冲突（非单射会导致**不同字段被映射到同一 SMT 符号**这一静默语义错误）。
//! 因此本实现把 `_` **一并转义**（`_` → `_u005F`），使输出中除自身发射的 `_uXXXX` 序列外不含任何 `_`，
//! 从而解码唯一、保证单射。码点 > `0xFFFF` 者用 6 位十六进制 `_UXXXXXX` 表示。
//! 该偏差已登记（见交付说明的 `INC-15`）。

/// 将任意标识符编码为 `[A-Za-z0-9_ua…]` 安全且**单射**的片段。
///
/// - ASCII 字母与数字：原样保留；
/// - 其余所有字符（**含 `_`**）：`_u` + 4 位大写十六进制（码点 ≤ `0xFFFF`）；
///   码点 > `0xFFFF` 时用 `_U` + 6 位大写十六进制。
pub fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 8);
    for ch in s.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch);
        } else if (ch as u32) <= 0xFFFF {
            out.push_str(&format!("_u{:04X}", ch as u32));
        } else {
            out.push_str(&format!("_U{:06X}", ch as u32));
        }
    }
    out
}

/// 展平标量符号 `NM-1`：`PL_<D>_<i>_<f>`。**单射**（`A-7`）。
pub fn scalar_symbol(domain: &str, index: usize, field: &str) -> String {
    format!("PL_{}_{}_{}", escape(domain), index, escape(field))
}

/// 域实例前缀 `domain_instance(D, i)`：`PL_<D>_<i>`。
pub fn domain_instance(domain: &str, index: usize) -> String {
    format!("PL_{}_{}", escape(domain), index)
}

/// 全局变量符号 `NM-2`：`PL_g_<escape(name)>`。
pub fn global_symbol(name: &str) -> String {
    format!("PL_g_{}", escape(name))
}

/// 标签长度上限（`NM-4`）。
const LABEL_MAX: usize = 128;

/// 标签总长超限时截断并追加 8 位 SHA-256 前缀（`NM-4`）。
fn clamp_label(mut label: String) -> String {
    if label.len() <= LABEL_MAX {
        return label;
    }
    use sha2::{Digest, Sha256};
    let mut h = Sha256::new();
    h.update(label.as_bytes());
    let digest = h.finalize();
    let suffix = hex::encode(&digest[..4]); // 8 个 hex 字符
    label.truncate(LABEL_MAX - 9);
    label.push('_');
    label.push_str(&suffix);
    label
}

/// 规则标签：`PLR__<policy>__<rule>`。
pub fn label_rule(policy: &str, rule: &str) -> String {
    clamp_label(format!(
        "PLR__{}__{}",
        escape(policy),
        escape(rule)
    ))
}

/// 分支标签：`PLB__<policy>__<branch>`。
pub fn label_branch(policy: &str, branch: &str) -> String {
    clamp_label(format!(
        "PLB__{}__{}",
        escape(policy),
        escape(branch)
    ))
}

/// 不变量否定标签：`PLI__<inv>`。
pub fn label_invariant(inv: &str) -> String {
    clamp_label(format!("PLI__{}", escape(inv)))
}

/// 互斥标签：`PLM__<policy>__<i>__<j>`。
pub fn label_mutex(policy: &str, i: usize, j: usize) -> String {
    clamp_label(format!("PLM__{}__{}__{}", escape(policy), i, j))
}

/// 覆盖性否定标签：`PLC__<policy>`。
pub fn label_completeness(policy: &str) -> String {
    clamp_label(format!("PLC__{}", escape(policy)))
}

/// 除零义务标签：`PLS__<policy>__DIVZERO`。
pub fn label_safety_divzero(policy: &str) -> String {
    clamp_label(format!("PLS__{}__DIVZERO", escape(policy)))
}

/// 旧策略否定标签：`PLR__<policy>__OLD_NEG`。
pub fn label_old_neg(policy: &str) -> String {
    clamp_label(format!("PLR__{}__OLD_NEG", escape(policy)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn escape_is_injective_on_adversarial_input() {
        // 回归：NM-4 原文的 `escape("-") == escape("_u002D")` 碰撞必须被消除。
        assert_ne!(escape("-"), escape("_u002D"));
        assert_ne!(escape("_"), escape("_u005F"));
    }

    #[test]
    fn scalar_symbol_injective_including_underscore_fields() {
        // A-7 的核心承诺：`db_host` 与 `db`+`host` 不得碰撞。
        let a = scalar_symbol("Services", 0, "db_host");
        let b = scalar_symbol("Services", 0, "db");
        let c = scalar_symbol("Services", 0, "host");
        assert_ne!(a, b);
        assert_ne!(b, c);
        assert_ne!(a, c);

        // 枚举全小规模域上验证单射（含保留字、下划线、Unicode）。
        let mut seen: HashMap<String, (String, usize, String)> = HashMap::new();
        for d in ["S", "s", "S_1"] {
            for i in 0..3usize {
                for f in ["id", "db", "host", "db_host", "div", "to_real", "_u002D", "-", "端口"] {
                    let sym = scalar_symbol(d, i, f);
                    if let Some(prev) = seen.insert(sym.clone(), (d.to_string(), i, f.to_string())) {
                        panic!("collision on {sym}: {:?} vs {:?}", prev, (d, i, f));
                    }
                }
            }
        }
    }

    #[test]
    fn label_over_length_is_clamped_and_deterministic() {
        let long = "a".repeat(200);
        let l1 = label_rule(&long, &long);
        let l2 = label_rule(&long, &long);
        assert_eq!(l1, l2);
        assert!(l1.len() <= LABEL_MAX);
    }
}
