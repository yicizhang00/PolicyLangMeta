//! Pest 集成层：文法嵌入、错误归一、P1/P2 边界（`02 §1.3` 的 ① Parser）。

use pest::error::{Error as PestError, LineColLocation};
use pest::Parser;
use pest_derive::Parser;

use policylang_ast::codes::E_BAD_HEADER;
use policylang_ast::diag::Diagnostic;
use policylang_ast::Span;

use crate::pair_map;

/// P1 词法 / P2 语法 的 Pest 解析器。
///
/// 文法路径为**源码相对路径**：`crates/policylang-parser/src/parse.rs` → `spec/grammar.pest`。
#[derive(Parser)]
#[grammar = "../../../spec/grammar.pest"]
pub struct PlmParser;

/// 解析错误码（`04 §11`）。语法级错误统一为 `E-SYNTAX`。
pub const E_SYNTAX: &str = "E-SYNTAX";

/// 把 Pest 的 `Error` 归一为 `Diagnostic`（携带精确 `Span`）。
///
/// 特判：源文件未以 `#lang` 开头且错误落在文件首字符时，归类为 `E-BAD-HEADER`
/// （比通用语法错误更可操作），与 `00 §0.6` 的「源文件头必需」一致。
fn normalize_error(err: PestError<Rule>, source: &str, path: Option<&str>) -> Diagnostic {
    let span = match err.line_col {
        LineColLocation::Pos((l, c)) => Span::new(l as u32, c as u32, l as u32, c as u32),
        LineColLocation::Span((l1, c1), (l2, c2)) => {
            Span::new(l1 as u32, c1 as u32, l2 as u32, c2 as u32)
        }
    };
    let where_ = path.map(|p| format!("{p}: ")).unwrap_or_default();

    let starts_with_header = source.trim_start().starts_with("#lang");
    if !starts_with_header && span.start_line == 1 && span.start_col == 1 {
        return Diagnostic::error(
            E_BAD_HEADER,
            format!(
                "{where_}缺少源文件头：`.plm` 必须以 `#lang policylang 2` 开头（00 §0.6）"
            ),
        )
        .with_span(span);
    }

    Diagnostic::error(E_SYNTAX, format!("{where_}语法错误：{err}")).with_span(span)
}

/// 解析一个 `.plm` 源文件。
///
/// 成功返回 `Ok(Spec)`；失败返回**全部**已发现的诊断（语法 + 语义构造期错误），
/// 满足 `02 §1.3` 的 `Result<Spec, Vec<Diagnostic>>` 契约。
pub fn parse_spec(source: &str, path: Option<&str>) -> Result<policylang_ast::Spec, Vec<Diagnostic>> {
    // 健壮性：剥离 UTF-8 BOM（规范要求无 BOM，但编辑器常会写入）
    let source = source.strip_prefix('\u{feff}').unwrap_or(source);
    let mut parse = match PlmParser::parse(Rule::spec_file, source) {
        Ok(p) => p,
        Err(e) => return Err(vec![normalize_error(e, source, path)]),
    };

    // `spec_file` 是顶层唯一产生式。
    let file = match parse.next() {
        Some(p) => p,
        None => {
            return Err(vec![Diagnostic::error(
                E_SYNTAX,
                "内部错误：解析器未产出 spec_file 根节点",
            )]);
        }
    };

    match pair_map::build_spec(file, source, path) {
        Ok(spec) => Ok(spec),
        Err(diags) => Err(diags),
    }
}

/// 人类可读的规则名（诊断与调试用）。
///
/// 关键字原子规则（`kw_*`）统一返回 `"keyword"`；其余规则给出精确名。
pub fn rule_name(rule: Rule) -> &'static str {
    match rule {
        Rule::spec_file => "spec_file",
        Rule::lang_header => "lang_header",
        Rule::version => "version",
        Rule::entity_decl => "entity_decl",
        Rule::field_decl => "field_decl",
        Rule::key_annotation => "key_annotation",
        Rule::domain_decl => "domain_decl",
        Rule::var_decl => "var_decl",
        Rule::type_expr => "type_expr",
        Rule::range_constraint => "range_constraint",
        Rule::policy_decl => "policy_decl",
        Rule::rule_decl => "rule_decl",
        Rule::branch_decl => "branch_decl",
        Rule::mutex_decl => "mutex_decl",
        Rule::invariant_decl => "invariant_decl",
        Rule::require_decl => "require_decl",
        Rule::waiver_decl => "waiver_decl",
        Rule::waiver_field => "waiver_field",
        Rule::waiver_key => "waiver_key",
        Rule::verify_decl => "verify_decl",
        Rule::formula => "formula",
        Rule::f_iff => "f_iff",
        Rule::f_implies => "f_implies",
        Rule::f_or => "f_or",
        Rule::f_and => "f_and",
        Rule::f_not => "f_not",
        Rule::f_primary => "f_primary",
        Rule::quantifier_expr => "quantifier_expr",
        Rule::distinct_marker => "distinct_marker",
        Rule::ident_list => "ident_list",
        Rule::matches_all_expr => "matches_all_expr",
        Rule::in_cidr_expr => "in_cidr_expr",
        Rule::in_range_expr => "in_range_expr",
        Rule::unique_expr => "unique_expr",
        Rule::interval_expr => "interval_expr",
        Rule::predicate => "predicate",
        Rule::cmp_op => "cmp_op",
        Rule::bool_atom => "bool_atom",
        Rule::expr => "expr",
        Rule::term => "term",
        Rule::add_op => "add_op",
        Rule::mul_op => "mul_op",
        Rule::factor => "factor",
        Rule::field_access => "field_access",
        Rule::str_len => "str_len",
        Rule::cast_expr => "cast_expr",
        Rule::bv_call => "bv_call",
        Rule::bv_op => "bv_op",
        Rule::number => "number",
        Rule::int_lit => "int_lit",
        Rule::bool_lit => "bool_lit",
        Rule::string_lit => "string_lit",
        Rule::escape_seq => "escape_seq",
        Rule::ident => "ident",
        Rule::reserved => "reserved",
        Rule::ident_char => "ident_char",
        Rule::decl => "decl",
        Rule::policy_item => "policy_item",
        Rule::str_char => "str_char",
        Rule::WHITESPACE => "WHITESPACE",
        Rule::COMMENT => "COMMENT",
        Rule::EOI => "EOI",
        // 关键字原子规则 kw_*
        _ => "keyword",
    }
}
