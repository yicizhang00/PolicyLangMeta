//! 诊断契约 —— 全部 crate 共享的 `Diagnostic`（`04 §11`、`spec/report.schema.json` `Diagnostic`）。
//!
//! 说明：`02 §2.1` 规定 `policylang-ast` 是「全部 crate 的公共数据契约」，而解析器、检查器的返回
//! 类型均为 `Result<_, Vec<Diagnostic>>`（`02 §1.3`），故 `Diagnostic` 落在本 crate 是契约的内在要求。

use serde::{Deserialize, Serialize};

use crate::span::Span;

/// 诊断严重级（与 `report.schema.json` 的 `severity` 枚举一致）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Error,
    Warning,
    Info,
}

impl Severity {
    pub fn as_str(self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Info => "info",
        }
    }
}

/// 修复模板 ID（`FIX-1`…`FIX-16`，`07 §7.4.2`）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum FixTemplateId {
    #[serde(rename = "FIX-1")]
    Fix1,
    #[serde(rename = "FIX-2")]
    Fix2,
    #[serde(rename = "FIX-3")]
    Fix3,
    #[serde(rename = "FIX-4")]
    Fix4,
    #[serde(rename = "FIX-5")]
    Fix5,
    #[serde(rename = "FIX-6")]
    Fix6,
    #[serde(rename = "FIX-7")]
    Fix7,
    #[serde(rename = "FIX-8")]
    Fix8,
    #[serde(rename = "FIX-9")]
    Fix9,
    #[serde(rename = "FIX-10")]
    Fix10,
    #[serde(rename = "FIX-11")]
    Fix11,
    #[serde(rename = "FIX-12")]
    Fix12,
    #[serde(rename = "FIX-13")]
    Fix13,
    #[serde(rename = "FIX-14")]
    Fix14,
    #[serde(rename = "FIX-15")]
    Fix15,
    #[serde(rename = "FIX-16")]
    Fix16,
}

impl FixTemplateId {
    pub fn as_str(self) -> &'static str {
        match self {
            FixTemplateId::Fix1 => "FIX-1",
            FixTemplateId::Fix2 => "FIX-2",
            FixTemplateId::Fix3 => "FIX-3",
            FixTemplateId::Fix4 => "FIX-4",
            FixTemplateId::Fix5 => "FIX-5",
            FixTemplateId::Fix6 => "FIX-6",
            FixTemplateId::Fix7 => "FIX-7",
            FixTemplateId::Fix8 => "FIX-8",
            FixTemplateId::Fix9 => "FIX-9",
            FixTemplateId::Fix10 => "FIX-10",
            FixTemplateId::Fix11 => "FIX-11",
            FixTemplateId::Fix12 => "FIX-12",
            FixTemplateId::Fix13 => "FIX-13",
            FixTemplateId::Fix14 => "FIX-14",
            FixTemplateId::Fix15 => "FIX-15",
            FixTemplateId::Fix16 => "FIX-16",
        }
    }
}

/// 一条诊断。机读判定**必须**使用 `code` 而非 `message`（`07 §7.1`）。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Diagnostic {
    pub code: String,
    pub severity: Severity,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<Span>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fix_template: Option<FixTemplateId>,
}

impl Diagnostic {
    pub fn error(code: &str, message: impl Into<String>) -> Self {
        Diagnostic {
            code: code.to_string(),
            severity: Severity::Error,
            message: message.into(),
            span: None,
            fix_template: None,
        }
    }

    pub fn warning(code: &str, message: impl Into<String>) -> Self {
        Diagnostic {
            code: code.to_string(),
            severity: Severity::Warning,
            message: message.into(),
            span: None,
            fix_template: None,
        }
    }

    pub fn info(code: &str, message: impl Into<String>) -> Self {
        Diagnostic {
            code: code.to_string(),
            severity: Severity::Info,
            message: message.into(),
            span: None,
            fix_template: None,
        }
    }

    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    pub fn maybe_span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    pub fn with_fix(mut self, fix: FixTemplateId) -> Self {
        self.fix_template = Some(fix);
        self
    }

    pub fn is_error(&self) -> bool {
        self.severity == Severity::Error
    }

    /// 面向终端的一行渲染：`error[E-XXX] L:C message`。
    pub fn render(&self) -> String {
        let loc = match self.span {
            Some(s) => format!("{}:{}", s.start_line, s.start_col),
            None => "-".to_string(),
        };
        let fix = self
            .fix_template
            .map(|f| format!(" [{}]", f.as_str()))
            .unwrap_or_default();
        format!(
            "{}[{}] {}: {}{}",
            self.severity.as_str(),
            self.code,
            loc,
            self.message,
            fix
        )
    }
}

/// 若 `diags` 含 `error` 级诊断则返回 `Err`，否则返回 `Ok(())`（统一的「错误优先」闸门）。
pub fn ensure_no_errors(diags: &[Diagnostic]) -> Result<(), Vec<Diagnostic>> {
    if diags.iter().any(Diagnostic::is_error) {
        Err(diags.to_vec())
    } else {
        Ok(())
    }
}
