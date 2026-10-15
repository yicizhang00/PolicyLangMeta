//! 源码跨度 `Span`（`05 §2.2`、`spec/report.schema.json` 的 `Span`）。
//!
//! 行列均为 **1 起**，`end` **不含**（半开区间），与 SARIF `region` 一致。

use serde::{Deserialize, Serialize};

/// 源码行列跨度。字段名与 `report.schema.json` 的 `Span` 严格一致。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Span {
    pub start_line: u32,
    pub start_col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

impl Span {
    pub const fn new(start_line: u32, start_col: u32, end_line: u32, end_col: u32) -> Self {
        Self {
            start_line,
            start_col,
            end_line,
            end_col,
        }
    }

    /// 合成一个语法单元的整体跨度（取并集）。
    pub fn merge(self, other: Span) -> Span {
        let (sl, sc) = if (self.start_line, self.start_col) <= (other.start_line, other.start_col) {
            (self.start_line, self.start_col)
        } else {
            (other.start_line, other.start_col)
        };
        let (el, ec) = if (self.end_line, self.end_col) >= (other.end_line, other.end_col) {
            (self.end_line, self.end_col)
        } else {
            (other.end_line, other.end_col)
        };
        Span::new(sl, sc, el, ec)
    }

    /// 供诊断文本使用的紧凑形（`L:C`）。
    pub fn loc(self) -> String {
        format!("{}:{}", self.start_line, self.start_col)
    }
}

impl Default for Span {
    fn default() -> Self {
        Span::new(1, 1, 1, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merge_takes_union() {
        let a = Span::new(1, 5, 1, 9);
        let b = Span::new(1, 7, 2, 3);
        assert_eq!(a.merge(b), Span::new(1, 5, 2, 3));
        assert_eq!(b.merge(a), Span::new(1, 5, 2, 3));
    }
}
