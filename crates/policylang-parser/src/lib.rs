//! `policylang-parser`（CR-1）— 以 Pest 解析 `.plm`，产出带 `Span` 的 `Spec`（`02 §2.2`、`04 §2`）。
//!
//! 文法为**单一事实源** `spec/grammar.pest`（编译期经 `include` 嵌入，无副本、无漂移）。

pub mod pair_map;
pub mod parse;

pub use parse::{parse_spec, PlmParser, Rule};
