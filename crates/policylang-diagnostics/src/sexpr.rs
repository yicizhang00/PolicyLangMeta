//! 极简 S-表达式解析（求解器响应的通用形态）。
//!
//! 支持：`(…)` 列表、原子、`"…"` 字串（`""` 转义）、`|…|` 引号符号、`;` 行注释。
//! 仅供解析求解器输出（model / unsat core / error），不做语义解释。

use std::fmt;

/// 解析错误。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub pos: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "S-Expr 解析错误 @{}: {}", self.pos, self.message)
    }
}

/// S-表达式。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SExpr {
    Atom(String),
    Str(String),
    List(Vec<SExpr>),
}

impl SExpr {
    pub fn as_atom(&self) -> Option<&str> {
        match self {
            SExpr::Atom(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_list(&self) -> Option<&[SExpr]> {
        match self {
            SExpr::List(v) => Some(v),
            _ => None,
        }
    }

    /// 头原子（列表首元素若为原子）。
    pub fn head(&self) -> Option<&str> {
        self.as_list()?.first()?.as_atom()
    }

    /// 是否为 `(error …)`。
    pub fn is_error(&self) -> bool {
        self.head() == Some("error")
    }

    /// 渲染回文本（用于诊断信息）。
    pub fn to_text(&self) -> String {
        match self {
            SExpr::Atom(a) => a.clone(),
            SExpr::Str(s) => format!("\"{s}\""),
            SExpr::List(v) => format!(
                "({})",
                v.iter().map(SExpr::to_text).collect::<Vec<_>>().join(" ")
            ),
        }
    }
}

/// 解析全部顶层表达式（忽略空白与注释）。
pub fn parse_all(input: &str) -> Result<Vec<SExpr>, ParseError> {
    let bytes: Vec<char> = input.chars().collect();
    let mut p = Parser {
        s: &bytes,
        pos: 0,
    };
    let mut out = Vec::new();
    loop {
        p.skip_trivia();
        if p.pos >= p.s.len() {
            return Ok(out);
        }
        out.push(p.expr()?);
    }
}

/// 解析首个表达式。
pub fn parse_one(input: &str) -> Result<SExpr, ParseError> {
    let all = parse_all(input)?;
    all.into_iter().next().ok_or(ParseError {
        pos: 0,
        message: "输入为空".into(),
    })
}

struct Parser<'a> {
    s: &'a [char],
    pos: usize,
}

impl Parser<'_> {
    fn peek(&self) -> Option<char> {
        self.s.get(self.pos).copied()
    }

    fn skip_trivia(&mut self) {
        loop {
            match self.peek() {
                Some(c) if c.is_whitespace() => self.pos += 1,
                Some(';') => {
                    while let Some(c) = self.peek() {
                        self.pos += 1;
                        if c == '\n' {
                            break;
                        }
                    }
                }
                _ => break,
            }
        }
    }

    fn expr(&mut self) -> Result<SExpr, ParseError> {
        self.skip_trivia();
        match self.peek() {
            None => Err(ParseError {
                pos: self.pos,
                message: "表达式意外结束".into(),
            }),
            Some('(') => {
                self.pos += 1;
                let mut items = Vec::new();
                loop {
                    self.skip_trivia();
                    match self.peek() {
                        Some(')') => {
                            self.pos += 1;
                            return Ok(SExpr::List(items));
                        }
                        None => {
                            return Err(ParseError {
                                pos: self.pos,
                                message: "列表缺少 `)`".into(),
                            })
                        }
                        _ => items.push(self.expr()?),
                    }
                }
            }
            Some(')') => Err(ParseError {
                pos: self.pos,
                message: "多余的 `)`".into(),
            }),
            Some('"') => self.string(),
            Some('|') => {
                self.pos += 1;
                let mut s = String::new();
                while let Some(c) = self.peek() {
                    self.pos += 1;
                    if c == '|' {
                        return Ok(SExpr::Atom(s));
                    }
                    if c == '\\' {
                        if let Some(n) = self.peek() {
                            self.pos += 1;
                            s.push(n);
                        }
                        continue;
                    }
                    s.push(c);
                }
                Err(ParseError {
                    pos: self.pos,
                    message: "引号符号缺少 `|`".into(),
                })
            }
            _ => {
                let mut s = String::new();
                while let Some(c) = self.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' {
                        break;
                    }
                    s.push(c);
                    self.pos += 1;
                }
                Ok(SExpr::Atom(s))
            }
        }
    }

    fn string(&mut self) -> Result<SExpr, ParseError> {
        self.pos += 1; // 起始引号
        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    return Err(ParseError {
                        pos: self.pos,
                        message: "字串缺少结束引号".into(),
                    })
                }
                Some('"') => {
                    self.pos += 1;
                    // SMT-LIB：`""` 表示一个字面双引号
                    if self.peek() == Some('"') {
                        self.pos += 1;
                        s.push('"');
                        continue;
                    }
                    return Ok(SExpr::Str(s));
                }
                Some(c) => {
                    s.push(c);
                    self.pos += 1;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_atoms_and_lists() {
        let e = parse_one("(sat)").unwrap();
        assert_eq!(e.head(), Some("sat"));
        let e = parse_one("((a 1) (b 2))").unwrap();
        assert_eq!(e.as_list().unwrap().len(), 2);
    }

    #[test]
    fn parses_quoted_and_evaluated_strings() {
        let e = parse_one(r#""a""b""#).unwrap();
        assert_eq!(e, SExpr::Str("a\"b".into()));
    }

    #[test]
    fn parses_multiple_toplevel_and_comments() {
        let all = parse_all("; comment\nsat\n(model)\n").unwrap();
        assert_eq!(all.len(), 2);
        assert_eq!(all[0].as_atom(), Some("sat"));
        assert_eq!(all[1].head(), Some("model"));
    }

    #[test]
    fn detects_errors_and_missing_paren() {
        assert!(parse_one("(error \"unknown\")").unwrap().is_error());
        assert!(parse_one("(a").is_err());
        assert!(parse_one(")").is_err());
    }
}
