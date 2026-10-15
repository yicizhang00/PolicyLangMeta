//! Pair 树 → AST 的构造（P2）。
//!
//! 职责边界（`02 §1.3` 的 ①）：
//! - 负责：把 Pest 的 `Pair` 树映射为带 `Span` 的强类型 AST；
//! - 负责：**字符串转义在此阶段解析为真实码点**（`06 §6.2.3` 明确要求，避免 P6 双重转义）；
//! - 不负责：类型检查、可判定性守卫、预算（属 CR-3）。
//!
//! 关键字在文法中是**原子规则** `kw_*`（见 `spec/grammar.pest` 的「实现期修正 · 词边界」），
//! 它们会作为 Pair 出现但不承载语义，故在 [`kids`] 中统一过滤。

use pest::iterators::Pair;

use policylang_ast::codes::*;
use policylang_ast::diag::Diagnostic;
use policylang_ast::formula::{
    ArithOp, Atom, BvOp, Cidr, CmpOp, Expr, ExprKind, Formula, FormulaKind, Rational, Sort,
};
use policylang_ast::spec::{
    BranchDecl, DomainDecl, EntityDecl, FieldDecl, InvariantDecl, MutexDecl, PolicyDecl,
    RangeConstraint, RequireDecl, RuleDecl, Spec, VarDecl, VerifyDecl, VerifyKind, WaiverDecl,
};
use policylang_ast::Span;

use crate::parse::Rule;

type Res<T> = Result<T, Diagnostic>;

fn err(code: &str, msg: impl Into<String>, span: Span) -> Diagnostic {
    Diagnostic::error(code, msg).with_span(span)
}

fn internal(span: Span, what: &str) -> Diagnostic {
    err(
        E_INTERNAL,
        format!("内部错误：AST 构造未预期的语法节点（{what}）"),
        span,
    )
}

/// 是否为关键字原子规则（无语义载荷）。
pub fn is_keyword(r: Rule) -> bool {
    use Rule::*;
    matches!(
        r,
        kw_entity
            | kw_domain
            | kw_var
            | kw_policy
            | kw_rule
            | kw_branch
            | kw_mutex
            | kw_invariant
            | kw_verify
            | kw_waiver
            | kw_require
            | kw_forall
            | kw_exists
            | kw_distinct
            | kw_in
            | kw_matches_all
            | kw_in_cidr
            | kw_in_range
            | kw_unique
            | kw_and
            | kw_or
            | kw_not
            | kw_implies
            | kw_iff
            | kw_Int
            | kw_Real
            | kw_Bool
            | kw_String
            | kw_IPv4
            | kw_IPv6
            | kw_BitVec
            | kw_Enum
            | kw_Set
            | kw_true
            | kw_false
            | kw_min
            | kw_max
            | kw_length
            | kw_size
            | kw_div
            | kw_mod
            | kw_consistency
            | kw_refines
            | kw_completeness
            | kw_safety
            | kw_under
            | kw_of
            | kw_to_real
            | kw_int2bv
            | kw_bv2int
            | kw_str_len
    )
}

/// 取子节点并**过滤关键字 Pair**（唯一的过滤点）。
fn kids(p: Pair<'_, Rule>) -> Vec<Pair<'_, Rule>> {
    p.into_inner().filter(|c| !is_keyword(c.as_rule())).collect()
}

/// 取 `Pair` 的源码跨度（pest 的 `line_col()` 为 1 起，与 `ast::Span` 一致）。
fn sp(p: &Pair<'_, Rule>) -> Span {
    let s = p.as_span();
    let (sl, sc) = s.start_pos().line_col();
    let (el, ec) = s.end_pos().line_col();
    Span::new(sl as u32, sc as u32, el as u32, ec as u32)
}

fn first_child<'a>(p: Pair<'a, Rule>, what: &str) -> Res<Pair<'a, Rule>> {
    let span = sp(&p);
    kids(p)
        .into_iter()
        .next()
        .ok_or_else(|| internal(span, what))
}

/// 断言 `Pair` 是预期规则，否则返回内部错误（防止文法演进导致的静默错映射）。
fn expect(pair: &Pair<'_, Rule>, want: Rule, span: Span) -> Res<()> {
    if pair.as_rule() == want {
        Ok(())
    } else {
        Err(internal(span, crate::parse::rule_name(pair.as_rule())))
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// 顶层
// ═════════════════════════════════════════════════════════════════════════════

/// 构造 `Spec`；**多错误收集**（声明级粒度继续解析，提升一次编译的诊断密度）。
pub fn build_spec(
    file: Pair<'_, Rule>,
    _source: &str,
    path: Option<&str>,
) -> Result<Spec, Vec<Diagnostic>> {
    let mut diags: Vec<Diagnostic> = Vec::new();
    let mut spec = Spec::empty(0);
    spec.source_path = path.map(str::to_string);

    let file_span = sp(&file);
    let mut seen_header = false;

    for p in file.into_inner() {
        match p.as_rule() {
            Rule::lang_header => {
                seen_header = true;
                match parse_header(&p) {
                    Ok(v) => spec.lang_version = v,
                    Err(d) => diags.push(d),
                }
            }
            Rule::EOI => {}
            Rule::entity_decl => match build_entity(p) {
                Ok(x) => spec.entities.push(x),
                Err(d) => diags.push(d),
            },
            Rule::domain_decl => match build_domain(p) {
                Ok(x) => spec.domains.push(x),
                Err(d) => diags.push(d),
            },
            Rule::var_decl => match build_var(p) {
                Ok(x) => spec.vars.push(x),
                Err(d) => diags.push(d),
            },
            Rule::policy_decl => match build_policy(p) {
                Ok(x) => spec.policies.push(x),
                Err(d) => diags.push(d),
            },
            Rule::invariant_decl => match build_invariant(p) {
                Ok(x) => spec.invariants.push(x),
                Err(d) => diags.push(d),
            },
            Rule::require_decl => match build_require(p) {
                Ok(x) => spec.requires.push(x),
                Err(d) => diags.push(d),
            },
            Rule::waiver_decl => match build_waiver(p) {
                Ok(x) => spec.waivers.push(x),
                Err(d) => diags.push(d),
            },
            Rule::verify_decl => match build_verify(p) {
                Ok(x) => spec.verifies.push(x),
                Err(d) => diags.push(d),
            },
            other => diags.push(internal(file_span, crate::parse::rule_name(other))),
        }
    }

    if !seen_header {
        diags.push(err(
            E_BAD_HEADER,
            "缺少源文件头：`.plm` 必须以 `#lang policylang <版本>` 开头（00 §0.6）",
            Span::new(1, 1, 1, 1),
        ));
    }

    if diags.iter().any(Diagnostic::is_error) {
        Err(diags)
    } else {
        Ok(spec)
    }
}

fn parse_header(p: &Pair<'_, Rule>) -> Res<u32> {
    let span = sp(p);
    let v = p
        .clone()
        .into_inner()
        .find(|c| c.as_rule() == Rule::version)
        .ok_or_else(|| internal(span, "lang_header 缺 version"))?;
    let n: u32 = v
        .as_str()
        .parse()
        .map_err(|_| err(E_BAD_HEADER, "`#lang` 版本号不是合法整数", span))?;
    if n != 2 {
        return Err(err(
            E_BAD_HEADER,
            format!("不支持的 DSL 版本 `{n}`：本实现仅支持 `#lang policylang 2`（00 §0.6）"),
            span,
        ));
    }
    Ok(n)
}

// ═════════════════════════════════════════════════════════════════════════════
// 声明
// ═════════════════════════════════════════════════════════════════════════════

fn build_entity(p: Pair<'_, Rule>) -> Res<EntityDecl> {
    let span = sp(&p);
    let mut name = None;
    let mut fields = Vec::new();
    for c in kids(p) {
        match c.as_rule() {
            Rule::ident => name = Some(c.as_str().to_string()),
            Rule::field_decl => fields.push(build_field(c)?),
            other => return Err(internal(span, crate::parse::rule_name(other))),
        }
    }
    Ok(EntityDecl {
        name: name.ok_or_else(|| internal(span, "entity_decl 缺名字"))?,
        fields,
        span,
    })
}

fn build_field(p: Pair<'_, Rule>) -> Res<FieldDecl> {
    let span = sp(&p);
    let mut is_key = false;
    let mut name = None;
    let mut sort = None;
    let mut range = None;
    for c in kids(p) {
        match c.as_rule() {
            Rule::key_annotation => is_key = true,
            Rule::ident => name = Some(c.as_str().to_string()),
            Rule::type_expr => sort = Some(parse_type_expr(&c)?),
            Rule::range_constraint => range = Some(parse_range_constraint(&c)?),
            other => return Err(internal(span, crate::parse::rule_name(other))),
        }
    }
    Ok(FieldDecl {
        name: name.ok_or_else(|| internal(span, "field_decl 缺字段名"))?,
        sort: sort.ok_or_else(|| internal(span, "field_decl 缺排序"))?,
        range,
        is_key,
        span,
    })
}

fn build_domain(p: Pair<'_, Rule>) -> Res<DomainDecl> {
    let span = sp(&p);
    let mut idents = Vec::new();
    let mut size = None;
    for c in kids(p) {
        match c.as_rule() {
            Rule::ident => idents.push(c.as_str().to_string()),
            Rule::int_lit => {
                size = Some(
                    c.as_str()
                        .parse::<u64>()
                        .map_err(|_| err(E_SYNTAX, "域 size 不是合法非负整数", sp(&c)))?,
                )
            }
            other => return Err(internal(span, crate::parse::rule_name(other))),
        }
    }
    if idents.len() != 2 {
        return Err(internal(span, "domain_decl 结构异常（期望 名 + 实体）"));
    }
    Ok(DomainDecl {
        name: idents[0].clone(),
        entity: idents[1].clone(),
        size: size.ok_or_else(|| internal(span, "domain_decl 缺 size"))?,
        span,
    })
}

fn build_var(p: Pair<'_, Rule>) -> Res<VarDecl> {
    let span = sp(&p);
    let mut name = None;
    let mut sort = None;
    let mut range = None;
    for c in kids(p) {
        match c.as_rule() {
            Rule::ident => name = Some(c.as_str().to_string()),
            Rule::type_expr => sort = Some(parse_type_expr(&c)?),
            Rule::range_constraint => range = Some(parse_range_constraint(&c)?),
            other => return Err(internal(span, crate::parse::rule_name(other))),
        }
    }
    Ok(VarDecl {
        name: name.ok_or_else(|| internal(span, "var_decl 缺名字"))?,
        sort: sort.ok_or_else(|| internal(span, "var_decl 缺排序"))?,
        range,
        span,
    })
}

fn build_named_formula(kind: Rule, p: Pair<'_, Rule>) -> Res<(String, Formula, Span)> {
    let s = sp(&p);
    let cs = kids(p);
    expect(
        cs.first().ok_or_else(|| internal(s, "缺名字"))?,
        Rule::ident,
        s,
    )?;
    let name = cs[0].as_str().to_string();
    let f = cs
        .get(1)
        .ok_or_else(|| internal(s, &format!("{} 缺公式", crate::parse::rule_name(kind))))?;
    let formula = build_formula(f.clone())?;
    Ok((name, formula, s))
}

fn build_policy(p: Pair<'_, Rule>) -> Res<PolicyDecl> {
    let span = sp(&p);
    let mut name = None;
    let mut rules = Vec::new();
    let mut branches = Vec::new();
    let mut mutexes = Vec::new();
    for c in kids(p) {
        match c.as_rule() {
            Rule::ident => name = Some(c.as_str().to_string()),
            Rule::rule_decl => {
                let (n, f, s) = build_named_formula(Rule::rule_decl, c)?;
                rules.push(RuleDecl {
                    name: n,
                    formula: f,
                    span: s,
                });
            }
            Rule::branch_decl => {
                let (n, f, s) = build_named_formula(Rule::branch_decl, c)?;
                branches.push(BranchDecl {
                    name: n,
                    formula: f,
                    span: s,
                });
            }
            Rule::mutex_decl => {
                let s = sp(&c);
                let names: Vec<String> = kids(c).iter().map(|x| x.as_str().to_string()).collect();
                mutexes.push(MutexDecl { names, span: s });
            }
            other => return Err(internal(span, crate::parse::rule_name(other))),
        }
    }
    Ok(PolicyDecl {
        name: name.ok_or_else(|| internal(span, "policy_decl 缺名字"))?,
        rules,
        branches,
        mutexes,
        span,
    })
}

fn build_invariant(p: Pair<'_, Rule>) -> Res<InvariantDecl> {
    let (name, formula, span) = build_named_formula(Rule::invariant_decl, p)?;
    Ok(InvariantDecl {
        name,
        formula,
        span,
    })
}

fn build_require(p: Pair<'_, Rule>) -> Res<RequireDecl> {
    let (name, formula, span) = build_named_formula(Rule::require_decl, p)?;
    Ok(RequireDecl {
        name,
        formula,
        span,
    })
}

fn build_waiver(p: Pair<'_, Rule>) -> Res<WaiverDecl> {
    let span = sp(&p);
    let mut name = None;
    let mut map: Vec<(String, String)> = Vec::new();
    for c in kids(p) {
        match c.as_rule() {
            Rule::ident => name = Some(c.as_str().to_string()),
            Rule::waiver_field => {
                let fs = sp(&c);
                let fc = kids(c);
                let k = fc
                    .first()
                    .ok_or_else(|| internal(fs, "waiver_field 缺键"))?
                    .as_str()
                    .to_string();
                let vp = fc.get(1).ok_or_else(|| internal(fs, "waiver_field 缺值"))?;
                let v = if vp.as_rule() == Rule::string_lit {
                    parse_string_lit(vp)?
                } else {
                    vp.as_str().to_string()
                };
                map.push((k, v));
            }
            other => return Err(internal(span, crate::parse::rule_name(other))),
        }
    }
    let get = |k: &str| map.iter().find(|(a, _)| a == k).map(|(_, v)| v.clone());
    let missing: Vec<&str> = ["target", "owner", "approver", "expires", "reason"]
        .into_iter()
        .filter(|k| get(k).is_none())
        .collect();
    let display = name.clone().unwrap_or_else(|| "<匿名>".into());
    if !missing.is_empty() {
        return Err(err(
            E_WAIVER_INCOMPLETE,
            format!(
                "waiver `{display}` 缺少必需字段：{}（07 §7.9 要求 target/owner/approver/expires/reason）",
                missing.join(", ")
            ),
            span,
        ));
    }
    let owner = get("owner").unwrap();
    let approver = get("approver").unwrap();
    if approver == owner {
        return Err(err(
            E_WAIVER_SELF_APPROVE,
            format!("waiver `{display}` 的 approver 与 owner 相同（`{owner}`）：审批人必须独立"),
            span,
        ));
    }
    Ok(WaiverDecl {
        name: name.ok_or_else(|| internal(span, "waiver_decl 缺名字"))?,
        target: get("target").unwrap(),
        owner,
        approver,
        expires: get("expires").unwrap(),
        reason: get("reason").unwrap(),
        span,
    })
}

fn build_verify(p: Pair<'_, Rule>) -> Res<VerifyDecl> {
    let span = sp(&p);
    let norm: String = p
        .as_str()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    let idents: Vec<String> = p
        .clone()
        .into_inner()
        .filter(|c| c.as_rule() == Rule::ident)
        .map(|c| c.as_str().to_string())
        .collect();

    let kind = if norm.contains(" refines ") {
        VerifyKind::Refines {
            new_policy: need(&idents, 0, &norm, span)?,
            old_policy: need(&idents, 1, &norm, span)?,
        }
    } else if norm.starts_with("verify consistency") {
        VerifyKind::Consistency {
            policy: need(&idents, 0, &norm, span)?,
        }
    } else if norm.starts_with("verify completeness") {
        VerifyKind::Completeness {
            policy: need(&idents, 0, &norm, span)?,
        }
    } else if norm.starts_with("verify safety") {
        VerifyKind::Safety {
            policy: need(&idents, 0, &norm, span)?,
        }
    } else if norm.starts_with("verify mutex") {
        VerifyKind::Mutex {
            policy: need(&idents, 0, &norm, span)?,
        }
    } else if norm.starts_with("verify invariant") {
        VerifyKind::Invariant {
            invariant: need(&idents, 0, &norm, span)?,
            policy: need(&idents, 1, &norm, span)?,
        }
    } else {
        return Err(err(
            E_SYNTAX,
            format!("无法识别的验证目标：`{norm}`（04 §7 的六式之一）"),
            span,
        ));
    };
    Ok(VerifyDecl { kind, span })
}

fn need(idents: &[String], i: usize, norm: &str, span: Span) -> Res<String> {
    idents
        .get(i)
        .cloned()
        .ok_or_else(|| err(E_SYNTAX, format!("`{norm}` 缺少必要的名称参数"), span))
}

// ═════════════════════════════════════════════════════════════════════════════
// 排序与范围
// ═════════════════════════════════════════════════════════════════════════════

fn parse_type_expr(p: &Pair<'_, Rule>) -> Res<Sort> {
    let span = sp(p);
    let text = p.as_str().trim();
    if text.starts_with("BitVec") {
        let w = p
            .clone()
            .into_inner()
            .find(|c| c.as_rule() == Rule::int_lit)
            .ok_or_else(|| internal(span, "BitVec 缺宽度"))?;
        let n: u32 = w
            .as_str()
            .parse()
            .map_err(|_| err(E_SORT_MISMATCH, "BitVec 宽度不是合法整数", span))?;
        if n == 0 || n > 1024 {
            return Err(err(
                E_SORT_MISMATCH,
                format!("BitVec 宽度 `{n}` 超出支持范围 1..=1024"),
                span,
            ));
        }
        return Ok(Sort::Bv(n));
    }
    if text.starts_with("Enum") {
        let members: Vec<String> = kids(p.clone())
            .iter()
            .filter(|c| c.as_rule() == Rule::ident)
            .map(|c| c.as_str().to_string())
            .collect();
        if members.is_empty() {
            return Err(err(E_BAD_SORT, "Enum 必须至少有一个成员", span));
        }
        return Ok(Sort::Enum(members));
    }
    match text {
        "Int" => Ok(Sort::Int),
        "Real" => Ok(Sort::Real),
        "Bool" => Ok(Sort::Bool),
        "String" => Ok(Sort::Str),
        "IPv4" => Ok(Sort::Bv(32)),
        "IPv6" => Ok(Sort::Bv(128)),
        other => Err(err(E_BAD_SORT, format!("未知排序 `{other}`"), span)),
    }
}

fn parse_range_constraint(p: &Pair<'_, Rule>) -> Res<RangeConstraint> {
    let span = sp(p);
    let children: Vec<Pair<'_, Rule>> = kids(p.clone())
        .into_iter()
        .filter(|c| matches!(c.as_rule(), Rule::number | Rule::int_lit))
        .collect();
    match children.first().map(|c| c.as_rule()) {
        Some(Rule::number) => {
            if children.len() != 2 {
                return Err(internal(span, "range_constraint(number) 结构异常"));
            }
            Ok(RangeConstraint::Numeric {
                min: parse_number_exact(&children[0])?,
                max: parse_number_exact(&children[1])?,
            })
        }
        Some(Rule::int_lit) => {
            if children.len() != 2 {
                return Err(internal(span, "range_constraint(length) 结构异常"));
            }
            Ok(RangeConstraint::Length {
                lo: children[0]
                    .as_str()
                    .parse::<u64>()
                    .map_err(|_| err(E_SYNTAX, "length 下界非法", span))?,
                hi: children[1]
                    .as_str()
                    .parse::<u64>()
                    .map_err(|_| err(E_SYNTAX, "length 上界非法", span))?,
            })
        }
        _ => Err(internal(span, "range_constraint 结构异常")),
    }
}

fn parse_number_exact(p: &Pair<'_, Rule>) -> Res<Rational> {
    let span = sp(p);
    Rational::parse_decimal(p.as_str())
        .ok_or_else(|| err(E_SYNTAX, format!("无法解析数值字面量 `{}`", p.as_str()), span))
}

// ═════════════════════════════════════════════════════════════════════════════
// 公式（优先级严格对应 03 §3.4.3）
// ═════════════════════════════════════════════════════════════════════════════

/// 构造公式。接受 `formula | f_iff | f_implies | f_or | f_and | f_not | f_primary`。
pub fn build_formula(p: Pair<'_, Rule>) -> Res<Formula> {
    let span = sp(&p);
    match p.as_rule() {
        Rule::formula => build_formula(first_child(p, "formula 为空")?),
        Rule::f_iff => {
            let cs = kids(p);
            let lhs = build_formula(cs.first().ok_or_else(|| internal(span, "f_iff 缺左"))?.clone())?;
            match cs.get(1) {
                Some(rhs) => {
                    let rhs = build_formula(rhs.clone())?;
                    let s = lhs.span.merge(rhs.span);
                    Ok(Formula::new(FormulaKind::Iff(Box::new(lhs), Box::new(rhs)), s))
                }
                None => Ok(lhs),
            }
        }
        Rule::f_implies => {
            let cs = kids(p);
            let lhs = build_formula(
                cs.first()
                    .ok_or_else(|| internal(span, "f_implies 缺左"))?
                    .clone(),
            )?;
            match cs.get(1) {
                Some(rhs) => {
                    let rhs = build_formula(rhs.clone())?;
                    let s = lhs.span.merge(rhs.span);
                    Ok(Formula::new(
                        FormulaKind::Implies(Box::new(lhs), Box::new(rhs)),
                        s,
                    ))
                }
                None => Ok(lhs),
            }
        }
        Rule::f_or => {
            let parts: Vec<Formula> = kids(p)
                .into_iter()
                .map(build_formula)
                .collect::<Res<Vec<_>>>()?;
            Ok(Formula::or(parts, span))
        }
        Rule::f_and => {
            let parts: Vec<Formula> = kids(p)
                .into_iter()
                .map(build_formula)
                .collect::<Res<Vec<_>>>()?;
            Ok(Formula::and(parts, span))
        }
        Rule::f_not => {
            let is_neg = p.as_str().trim_start().starts_with("not");
            let inner = build_formula(first_child(p, "f_not 为空")?)?;
            if is_neg {
                Ok(Formula::new(FormulaKind::Not(Box::new(inner)), span))
            } else {
                Ok(inner)
            }
        }
        Rule::f_primary => {
            let child = first_child(p, "f_primary 为空")?;
            match child.as_rule() {
                Rule::formula => build_formula(child),
                Rule::quantifier_expr => build_quantifier(child),
                Rule::matches_all_expr => build_matches_all(child),
                Rule::in_cidr_expr => build_in_cidr(child),
                Rule::in_range_expr => build_in_range(child),
                Rule::unique_expr => build_unique(child),
                Rule::interval_expr => build_interval(child),
                Rule::predicate => build_predicate(child),
                Rule::bool_atom => {
                    let e = first_child(child, "bool_atom 为空")?;
                    let e = build_expr(e)?;
                    let s = e.span;
                    Ok(Formula::new(FormulaKind::Atom(Atom::Bool(e)), s))
                }
                other => Err(internal(span, crate::parse::rule_name(other))),
            }
        }
        other => Err(internal(span, crate::parse::rule_name(other))),
    }
}

fn build_quantifier(p: Pair<'_, Rule>) -> Res<Formula> {
    let span = sp(&p);
    let is_forall = p.as_str().trim_start().starts_with("forall");
    let mut vars: Vec<String> = Vec::new();
    let mut domain = None;
    let mut distinct = false;
    let mut body = None;

    for c in kids(p) {
        match c.as_rule() {
            Rule::ident_list => {
                vars = kids(c).iter().map(|x| x.as_str().to_string()).collect();
            }
            Rule::ident => {
                if domain.is_none() {
                    domain = Some(c.as_str().to_string());
                } else {
                    return Err(internal(span, "quantifier_expr 出现多余 ident"));
                }
            }
            Rule::distinct_marker => distinct = true,
            _ => body = Some(build_formula(c)?),
        }
    }

    if vars.is_empty() {
        return Err(err(E_SYNTAX, "量词缺少绑定变量列表", span));
    }
    let domain = domain.ok_or_else(|| err(E_SYNTAX, "量词缺少 `in <域>`", span))?;
    let body = body.ok_or_else(|| err(E_SYNTAX, "量词缺少体公式", span))?;

    let kind = if is_forall {
        FormulaKind::Forall {
            vars,
            domain,
            distinct,
            body: Box::new(body),
        }
    } else {
        FormulaKind::Exists {
            vars,
            domain,
            distinct,
            body: Box::new(body),
        }
    };
    Ok(Formula::new(kind, span))
}

fn build_matches_all(p: Pair<'_, Rule>) -> Res<Formula> {
    let span = sp(&p);
    let mut subject = None;
    let mut patterns = Vec::new();
    for c in kids(p) {
        match c.as_rule() {
            Rule::expr => subject = Some(build_expr(c)?),
            Rule::string_lit => patterns.push(parse_string_lit(&c)?),
            other => return Err(internal(span, crate::parse::rule_name(other))),
        }
    }
    Ok(Formula::new(
        FormulaKind::MatchesAll {
            subject: subject.ok_or_else(|| internal(span, "matches_all 缺被匹配表达式"))?,
            patterns,
        },
        span,
    ))
}

fn build_in_cidr(p: Pair<'_, Rule>) -> Res<Formula> {
    let span = sp(&p);
    let mut subject = None;
    let mut cidr = None;
    for c in kids(p) {
        match c.as_rule() {
            Rule::expr => subject = Some(build_expr(c)?),
            Rule::string_lit => {
                let text = parse_string_lit(&c)?;
                cidr = Some(parse_cidr(&text, sp(&c))?);
            }
            other => return Err(internal(span, crate::parse::rule_name(other))),
        }
    }
    Ok(Formula::new(
        FormulaKind::InCidr {
            subject: subject.ok_or_else(|| internal(span, "in_cidr 缺表达式"))?,
            cidr: cidr.ok_or_else(|| internal(span, "in_cidr 缺网段字面量"))?,
        },
        span,
    ))
}

fn build_in_range(p: Pair<'_, Rule>) -> Res<Formula> {
    let span = sp(&p);
    let mut subject = None;
    let mut ips: Vec<String> = Vec::new();
    for c in kids(p) {
        match c.as_rule() {
            Rule::expr => subject = Some(build_expr(c)?),
            Rule::string_lit => ips.push(parse_string_lit(&c)?),
            other => return Err(internal(span, crate::parse::rule_name(other))),
        }
    }
    if ips.len() != 2 {
        return Err(err(E_CIDR_INVALID, "`in_range` 需要恰好两个地址字面量", span));
    }
    let (w1, lo) = parse_ip(&ips[0], span)?;
    let (w2, hi) = parse_ip(&ips[1], span)?;
    if w1 != w2 {
        return Err(err(
            E_CIDR_INVALID,
            format!("`in_range` 两端地址族不一致（{w1} 位 vs {w2} 位）"),
            span,
        ));
    }
    if lo > hi {
        return Err(err(
            E_CIDR_INVALID,
            format!("`in_range` 下界 {} 大于上界 {}", ips[0], ips[1]),
            span,
        ));
    }
    Ok(Formula::new(
        FormulaKind::InRange {
            subject: subject.ok_or_else(|| internal(span, "in_range 缺表达式"))?,
            lo: ips[0].clone(),
            hi: ips[1].clone(),
            width: w1,
            lo_val: lo,
            hi_val: hi,
        },
        span,
    ))
}

fn build_unique(p: Pair<'_, Rule>) -> Res<Formula> {
    let span = sp(&p);
    let idents: Vec<String> = kids(p).iter().map(|c| c.as_str().to_string()).collect();
    if idents.len() != 2 {
        return Err(internal(span, "unique_expr 需要 (域, 字段) 两个标识符"));
    }
    Ok(Formula::new(
        FormulaKind::Unique {
            domain: idents[0].clone(),
            field: idents[1].clone(),
        },
        span,
    ))
}

/// `x in [a..b]` ⟺ `a ≤ x ∧ x ≤ b`（`03 §3.4.2 T-INRANGE`）。
fn build_interval(p: Pair<'_, Rule>) -> Res<Formula> {
    let span = sp(&p);
    let exprs: Vec<Expr> = kids(p).into_iter().map(build_expr).collect::<Res<Vec<_>>>()?;
    if exprs.len() != 3 {
        return Err(internal(span, "interval_expr 需要 (x, a, b) 三个表达式"));
    }
    let (x, a, b) = (exprs[0].clone(), exprs[1].clone(), exprs[2].clone());
    let ge = Formula::new(
        FormulaKind::Atom(Atom::Cmp {
            lhs: x.clone(),
            op: CmpOp::Ge,
            rhs: a,
        }),
        span,
    );
    let le = Formula::new(
        FormulaKind::Atom(Atom::Cmp {
            lhs: x,
            op: CmpOp::Le,
            rhs: b,
        }),
        span,
    );
    Ok(Formula::and(vec![ge, le], span))
}

fn build_predicate(p: Pair<'_, Rule>) -> Res<Formula> {
    let span = sp(&p);
    let cs = kids(p);
    let lhs = build_expr(cs.first().ok_or_else(|| internal(span, "predicate 缺左操作数"))?.clone())?;
    let op_pair = cs.get(1).ok_or_else(|| internal(span, "predicate 缺比较符"))?;
    let op = match op_pair.as_str().trim() {
        "==" => CmpOp::Eq,
        "!=" => CmpOp::Ne,
        "<" => CmpOp::Lt,
        "<=" => CmpOp::Le,
        ">" => CmpOp::Gt,
        ">=" => CmpOp::Ge,
        "str.<" => CmpOp::StrLt,
        "str.<=" => CmpOp::StrLe,
        other => return Err(internal(span, &format!("未知比较符 `{other}`"))),
    };
    let rhs = build_expr(cs.get(2).ok_or_else(|| internal(span, "predicate 缺右操作数"))?.clone())?;
    Ok(Formula::new(FormulaKind::Atom(Atom::Cmp { lhs, op, rhs }), span))
}

// ═════════════════════════════════════════════════════════════════════════════
// 表达式
// ═════════════════════════════════════════════════════════════════════════════

/// 构造表达式。接受 `expr | term | factor`。
pub fn build_expr(p: Pair<'_, Rule>) -> Res<Expr> {
    let span = sp(&p);
    match p.as_rule() {
        Rule::expr => {
            let cs = kids(p);
            let mut acc = build_expr(cs.first().ok_or_else(|| internal(span, "expr 为空"))?.clone())?;
            let mut i = 1;
            while i + 1 < cs.len() + 1 {
                let Some(op) = cs.get(i) else { break };
                let op_kind = match op.as_str().trim() {
                    "+" => ArithOp::Add,
                    "-" => ArithOp::Sub,
                    other => return Err(internal(span, &format!("未知加法符 `{other}`"))),
                };
                let rhs = cs
                    .get(i + 1)
                    .ok_or_else(|| internal(span, "expr 运算符后缺操作数"))?;
                let rhs = build_expr(rhs.clone())?;
                let s = acc.span.merge(rhs.span);
                acc = Expr::new(
                    ExprKind::Arith {
                        op: op_kind,
                        lhs: Box::new(acc),
                        rhs: Box::new(rhs),
                    },
                    s,
                );
                i += 2;
            }
            Ok(acc)
        }
        Rule::term => {
            let cs = kids(p);
            let mut acc = build_expr(cs.first().ok_or_else(|| internal(span, "term 为空"))?.clone())?;
            let mut i = 1;
            while i + 1 < cs.len() + 1 {
                let Some(op) = cs.get(i) else { break };
                let op_kind = match op.as_str().trim() {
                    "*" => ArithOp::Mul,
                    "/" => ArithOp::RealDiv,
                    "div" => ArithOp::IntDiv,
                    "mod" => ArithOp::IntMod,
                    other => return Err(internal(span, &format!("未知乘法符 `{other}`"))),
                };
                let rhs = cs
                    .get(i + 1)
                    .ok_or_else(|| internal(span, "term 运算符后缺操作数"))?;
                let rhs = build_expr(rhs.clone())?;
                let s = acc.span.merge(rhs.span);
                acc = Expr::new(
                    ExprKind::Arith {
                        op: op_kind,
                        lhs: Box::new(acc),
                        rhs: Box::new(rhs),
                    },
                    s,
                );
                i += 2;
            }
            Ok(acc)
        }
        Rule::factor => {
            let child = first_child(p, "factor 为空")?;
            build_factor_child(child, span)
        }
        other => Err(internal(span, crate::parse::rule_name(other))),
    }
}

fn build_factor_child(child: Pair<'_, Rule>, span: Span) -> Res<Expr> {
    match child.as_rule() {
        Rule::expr => build_expr(child),
        Rule::factor => {
            let inner = build_expr(child)?;
            Ok(Expr::new(ExprKind::Neg(Box::new(inner)), span))
        }
        Rule::number => {
            let r = parse_number_exact(&child)?;
            if r.is_integer() {
                Ok(Expr::new(ExprKind::IntLit(r.num), span))
            } else {
                Ok(Expr::new(ExprKind::RealLit(r), span))
            }
        }
        Rule::int_lit => {
            let v: i128 = child
                .as_str()
                .parse()
                .map_err(|_| err(E_SYNTAX, "整数字面量溢出 i128", span))?;
            Ok(Expr::new(ExprKind::IntLit(v), span))
        }
        Rule::bool_lit => Ok(Expr::new(
            ExprKind::BoolLit(child.as_str().trim() == "true"),
            span,
        )),
        Rule::string_lit => {
            let s = parse_string_lit(&child)?;
            Ok(Expr::new(ExprKind::StrLit(s), span))
        }
        Rule::ident => Ok(Expr::new(ExprKind::Var(child.as_str().to_string()), span)),
        Rule::field_access => {
            let cs = kids(child);
            let instance = cs
                .first()
                .ok_or_else(|| internal(span, "field_access 缺实例"))?
                .as_str()
                .to_string();
            let field = cs
                .get(1)
                .ok_or_else(|| internal(span, "field_access 缺字段"))?
                .as_str()
                .to_string();
            Ok(Expr::new(ExprKind::FieldAccess { instance, field }, span))
        }
        Rule::str_len => {
            let e = first_child(child, "str_len 缺参数")?;
            let e = build_expr(e)?;
            Ok(Expr::new(ExprKind::StrLen(Box::new(e)), span))
        }
        Rule::bv_call => {
            let cs = kids(child);
            let op_pair = cs.first().ok_or_else(|| internal(span, "bv_call 缺运算名"))?;
            let op = match op_pair.as_str().trim() {
                "bvand" => BvOp::And,
                "bvor" => BvOp::Or,
                "bvxor" => BvOp::Xor,
                "bvnot" => BvOp::Not,
                "bvadd" => BvOp::Add,
                "bvsub" => BvOp::Sub,
                "bvmul" => BvOp::Mul,
                "bvshl" => BvOp::Shl,
                "bvlshr" => BvOp::Lshr,
                other => return Err(internal(span, &format!("未知位向量运算 `{other}`"))),
            };
            let lhs = build_expr(cs.get(1).ok_or_else(|| internal(span, "bv_call 缺第一参数"))?.clone())?;
            let rhs = build_expr(cs.get(2).ok_or_else(|| internal(span, "bv_call 缺第二参数"))?.clone())?;
            let width = match &lhs.kind {
                ExprKind::Bv { width, .. } => *width,
                _ => 32,
            };
            Ok(Expr::new(
                ExprKind::Bv {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    width,
                },
                span,
            ))
        }
        Rule::cast_expr => build_cast(child, span),
        other => Err(internal(span, crate::parse::rule_name(other))),
    }
}

fn build_cast(child: Pair<'_, Rule>, span: Span) -> Res<Expr> {
    let text = child.as_str().trim();
    let cs = kids(child);
    if text.starts_with("to_real") {
        let e = build_expr(cs.first().ok_or_else(|| internal(span, "to_real 缺参数"))?.clone())?;
        return Ok(Expr::new(ExprKind::ToReal(Box::new(e)), span));
    }
    if text.starts_with("int2bv") {
        let w = cs
            .first()
            .ok_or_else(|| internal(span, "int2bv 缺宽度"))?
            .as_str()
            .parse::<u32>()
            .map_err(|_| err(E_SORT_MISMATCH, "int2bv 宽度非法", span))?;
        let e = build_expr(cs.get(1).ok_or_else(|| internal(span, "int2bv 缺参数"))?.clone())?;
        return Ok(Expr::new(
            ExprKind::Int2Bv {
                width: w,
                value: Box::new(e),
            },
            span,
        ));
    }
    if text.starts_with("bv2int") {
        let e = build_expr(cs.first().ok_or_else(|| internal(span, "bv2int 缺参数"))?.clone())?;
        return Ok(Expr::new(ExprKind::Bv2Int(Box::new(e)), span));
    }
    Err(internal(span, "未知类型转换"))
}

// ═════════════════════════════════════════════════════════════════════════════
// 字面量：字符串转义与 IP/CIDR
// ═════════════════════════════════════════════════════════════════════════════

/// 解析字符串字面量并把转义**在此阶段**还原为真实码点（`06 §6.2.3`）。
pub fn parse_string_lit(p: &Pair<'_, Rule>) -> Res<String> {
    let raw = p.as_str();
    let span = sp(p);
    if raw.len() < 2 {
        return Err(err(E_SYNTAX, "字符串字面量过短", span));
    }
    let body = &raw[1..raw.len() - 1]; // 去掉两侧 ASCII 引号
    let mut out = String::with_capacity(body.len());
    let mut chars = body.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        let esc = chars
            .next()
            .ok_or_else(|| err(E_SYNTAX, "字符串以孤立反斜杠结尾", span))?;
        match esc {
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            'n' => out.push('\n'),
            't' => out.push('\t'),
            'r' => out.push('\r'),
            'x' | 'u' => {
                let n = if esc == 'x' { 2 } else { 4 };
                let mut h = String::new();
                for _ in 0..n {
                    h.push(
                        chars
                            .next()
                            .ok_or_else(|| err(E_SYNTAX, format!("\\{esc} 转义位数不足"), span))?,
                    );
                }
                let v = u32::from_str_radix(&h, 16)
                    .map_err(|_| err(E_SYNTAX, format!("`\\{esc}{h}` 不是合法十六进制"), span))?;
                out.push(
                    char::from_u32(v)
                        .ok_or_else(|| err(E_SYNTAX, format!("`\\{esc}{h}` 不是合法码点"), span))?,
                );
            }
            other => {
                return Err(err(
                    E_SYNTAX,
                    format!("不支持的转义 `\\{other}`（04 §2 允许 \\\\ \\\" \\n \\t \\r \\xHH \\uHHHH）"),
                    span,
                ));
            }
        }
    }
    Ok(out)
}

/// 解析 CIDR 字面量 `a.b.c.d/p` 或 `2001:db8::/32`（`03 §3.12.3`）。
pub fn parse_cidr(text: &str, span: Span) -> Res<Cidr> {
    let (addr, prefix_s) = text
        .split_once('/')
        .ok_or_else(|| err(E_CIDR_INVALID, format!("CIDR `{text}` 缺少 `/前缀长度`"), span))?;
    let prefix: u32 = prefix_s
        .trim()
        .parse()
        .map_err(|_| err(E_CIDR_INVALID, format!("CIDR `{text}` 前缀长度非法"), span))?;
    let (width, addr_val) = parse_ip(addr, span)?;
    if prefix > width {
        return Err(err(
            E_CIDR_INVALID,
            format!("CIDR `{text}` 前缀长度 {prefix} 超过地址位宽 {width}"),
            span,
        ));
    }
    let full: u128 = if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    let host: u128 = if prefix >= width {
        0
    } else {
        (1u128 << (width - prefix)) - 1
    };
    let mask = if prefix == 0 { 0 } else { full & !host };
    let net0 = addr_val & mask;
    if net0 != addr_val {
        return Err(err(
            E_CIDR_INVALID,
            format!(
                "CIDR `{text}` 的地址不是该前缀下的网络地址（主机位必须为 0），请改为 `{}/{}`",
                format_ip(net0, width),
                prefix
            ),
            span,
        ));
    }
    Ok(Cidr {
        width,
        net0,
        prefix,
        text: text.to_string(),
    })
}

/// 解析 IP 地址，返回 `(位宽, 无符号大端值)`。
pub fn parse_ip(text: &str, span: Span) -> Res<(u32, u128)> {
    let t = text.trim();
    if t.contains(':') {
        let v = parse_ipv6(t).ok_or_else(|| err(E_CIDR_INVALID, format!("非法 IPv6 地址 `{t}`"), span))?;
        Ok((128, v))
    } else {
        let v = parse_ipv4(t).ok_or_else(|| err(E_CIDR_INVALID, format!("非法 IPv4 地址 `{t}`"), span))?;
        Ok((32, v as u128))
    }
}

fn parse_ipv4(t: &str) -> Option<u32> {
    let parts: Vec<&str> = t.split('.').collect();
    if parts.len() != 4 {
        return None;
    }
    let mut v: u32 = 0;
    for p in parts {
        if p.is_empty() || p.len() > 3 || !p.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        let n: u32 = p.parse().ok()?;
        if n > 255 {
            return None;
        }
        v = (v << 8) | n;
    }
    Some(v)
}

fn parse_ipv6(t: &str) -> Option<u128> {
    let (left, right) = match t.split_once("::") {
        Some((a, b)) => {
            if b.contains("::") {
                return None;
            }
            (a, Some(b))
        }
        None => (t, None),
    };
    let parse_groups = |s: &str| -> Option<Vec<u16>> {
        if s.is_empty() {
            return Some(Vec::new());
        }
        s.split(':')
            .map(|g| {
                if g.is_empty() || g.len() > 4 || !g.chars().all(|c| c.is_ascii_hexdigit()) {
                    None
                } else {
                    u16::from_str_radix(g, 16).ok()
                }
            })
            .collect()
    };
    let l = parse_groups(left)?;
    let r = match right {
        Some(s) => parse_groups(s)?,
        None => Vec::new(),
    };
    let mut groups: Vec<u16> = Vec::with_capacity(8);
    groups.extend_from_slice(&l);
    if right.is_some() {
        let fill = 8usize.checked_sub(l.len() + r.len())?;
        if fill == 0 {
            return None; // `::` 至少压缩一组
        }
        groups.extend(std::iter::repeat(0u16).take(fill));
    }
    groups.extend_from_slice(&r);
    if groups.len() != 8 {
        return None;
    }
    let mut v: u128 = 0;
    for g in groups {
        v = (v << 16) | g as u128;
    }
    Some(v)
}

/// 把无符号值按位宽格式化为点分十进制（IPv4）或冒号分组（IPv6）。
pub fn format_ip(v: u128, width: u32) -> String {
    if width == 32 {
        format!(
            "{}.{}.{}.{}",
            (v >> 24) & 0xff,
            (v >> 16) & 0xff,
            (v >> 8) & 0xff,
            v & 0xff
        )
    } else {
        (0..8)
            .map(|i| format!("{:x}", (v >> (112 - 16 * i)) & 0xffff))
            .collect::<Vec<_>>()
            .join(":")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::{parse_spec, Rule as R};
    use pest::Parser;

    fn ok(src: &str) -> Spec {
        parse_spec(src, None).unwrap_or_else(|d| panic!("应解析成功，实际诊断：{d:?}"))
    }

    #[test]
    fn parses_grammar_smoke() {
        let s = ok("#lang policylang 2\nentity E { a: Int [min: 1, max: 3], }\n");
        assert_eq!(s.lang_version, 2);
        assert_eq!(s.entities.len(), 1);
        assert_eq!(s.entities[0].fields[0].name, "a");
    }

    #[test]
    fn keyword_boundary_is_enforced() {
        // `Integer` 必须是合法标识符（不得被 `Int` 的关键字边界误伤）
        let s = ok("#lang policylang 2\nentity Integer { a: Int }\n");
        assert_eq!(s.entities[0].name, "Integer");
        // 保留字不得作标识符
        assert!(parse_spec("#lang policylang 2\nentity Int { a: Int }\n", None).is_err());
        // `forall x index:` 这类拼接不得被误解析
        assert!(parse_spec(
            "#lang policylang 2\nentity E { a: Int }\ndomain D: Set[E] [size: 1]\n\
             policy P { rule R: forall x in D: x.a >= 1 }\n",
            None
        )
        .is_ok());
    }

    #[test]
    fn string_escapes_are_resolved_at_ast_layer() {
        let mut p = crate::parse::PlmParser::parse(R::string_lit, r#""a\n\t\\\"\x41\u0042""#).unwrap();
        let lit = p.next().unwrap();
        assert_eq!(parse_string_lit(&lit).unwrap(), "a\n\t\\\"AB");
    }

    #[test]
    fn interval_becomes_conjunction() {
        let s = ok("#lang policylang 2\nvar x: Int\nrequire R: x in [1..10]\n");
        match &s.requires[0].formula.kind {
            FormulaKind::And(v) => assert_eq!(v.len(), 2),
            other => panic!("期望 And，实际 {other:?}"),
        }
    }

    #[test]
    fn precedence_iff_lowest_and_or_ordering() {
        let s = ok("#lang policylang 2\nvar a: Bool\nvar b: Bool\nvar c: Bool\nrequire R: a and b iff c\n");
        match &s.requires[0].formula.kind {
            FormulaKind::Iff(_, _) => {}
            other => panic!("iff 应为最低优先级，实际 {other:?}"),
        }
        // a or b and c ==> or(a, and(b,c))
        let s2 = ok("#lang policylang 2\nvar a: Bool\nvar b: Bool\nvar c: Bool\nrequire R: a or b and c\n");
        match &s2.requires[0].formula.kind {
            FormulaKind::Or(v) => {
                assert_eq!(v.len(), 2);
                assert!(matches!(v[1].kind, FormulaKind::And(_)));
            }
            other => panic!("or 应高于 and，实际 {other:?}"),
        }
    }

    #[test]
    fn not_is_parsed() {
        let s = ok("#lang policylang 2\nvar a: Bool\nrequire R: not a\n");
        assert!(matches!(s.requires[0].formula.kind, FormulaKind::Not(_)));
    }

    #[test]
    fn quantifier_distinct_parsed() {
        let s = ok(
            "#lang policylang 2\nentity E { a: Int }\ndomain D: Set[E] [size: 3]\n\
             policy P { rule R: forall x, y in D distinct: x.a != y.a }\n",
        );
        match &s.policies[0].rules[0].formula.kind {
            FormulaKind::Forall { vars, distinct, .. } => {
                assert_eq!(vars.len(), 2);
                assert!(*distinct);
            }
            other => panic!("期望 Forall，实际 {other:?}"),
        }
        let s2 = ok(
            "#lang policylang 2\nentity E { a: Int }\ndomain D: Set[E] [size: 3]\n\
             policy P { rule R: exists x in D: x.a > 0 }\n",
        );
        assert!(matches!(
            s2.policies[0].rules[0].formula.kind,
            FormulaKind::Exists { distinct: false, .. }
        ));
    }

    #[test]
    fn full_cloud_example_parses() {
        let src = include_str!("../../../examples/cloud-deployment.plm");
        let s = ok(src);
        assert!(s.entities.len() >= 1);
        assert!(s.domains.len() >= 1);
        assert!(s.policies.len() >= 3);
        assert!(s.waivers.len() == 1);
        assert!(s.verifies.len() >= 4);
    }

    #[test]
    fn all_examples_parse() {
        for (name, src) in [
            ("cloud", include_str!("../../../examples/cloud-deployment.plm")),
            (
                "exchange",
                include_str!("../../../examples/exchange-compliance.plm"),
            ),
            (
                "coupon",
                include_str!("../../../examples/marketing-coupon.plm"),
            ),
        ] {
            let r = parse_spec(src, Some(name));
            assert!(r.is_ok(), "示例 {name} 应可解析：{:?}", r.err());
        }
    }

    #[test]
    fn cidr_parsing_and_alignment_check() {
        let s = ok(
            "#lang policylang 2\nentity E { ip: IPv4 }\ndomain D: Set[E] [size: 1]\n\
             invariant I { forall x in D: in_cidr(x.ip, \"10.0.1.0/24\") }\n",
        );
        match &s.invariants[0].formula.kind {
            FormulaKind::Forall { body, .. } => match &body.kind {
                FormulaKind::InCidr { cidr, .. } => {
                    assert_eq!(cidr.width, 32);
                    assert_eq!(cidr.prefix, 24);
                    assert_eq!(cidr.net0, 0x0A00_0100);
                    assert_eq!(cidr.mask(), 0xFFFF_FF00);
                }
                other => panic!("期望 InCidr，实际 {other:?}"),
            },
            other => panic!("期望 Forall，实际 {other:?}"),
        }
        assert!(parse_spec(
            "#lang policylang 2\nentity E { ip: IPv4 }\ndomain D: Set[E] [size: 1]\n\
             invariant I { forall x in D: in_cidr(x.ip, \"10.0.1.5/24\") }\n",
            None
        )
        .is_err());
    }

    #[test]
    fn verify_forms_classified() {
        let s = ok(
            "#lang policylang 2\npolicy A { rule R: true }\npolicy B { rule R: true }\n\
             invariant I { true }\n\
             verify consistency of A\nverify invariant I under A\nverify A refines B\n\
             verify completeness of A\nverify safety of A\nverify mutex of A\n",
        );
        assert_eq!(s.verifies.len(), 6);
        assert!(matches!(s.verifies[0].kind, VerifyKind::Consistency { .. }));
        assert!(matches!(s.verifies[1].kind, VerifyKind::Invariant { .. }));
        assert!(matches!(s.verifies[2].kind, VerifyKind::Refines { .. }));
        assert!(matches!(s.verifies[3].kind, VerifyKind::Completeness { .. }));
        assert!(matches!(s.verifies[4].kind, VerifyKind::Safety { .. }));
        assert!(matches!(s.verifies[5].kind, VerifyKind::Mutex { .. }));
        assert_eq!(s.verifies[0].kind.check_name(), "A::consistency::Consistency");
    }

    #[test]
    fn key_annotation_parsed() {
        let s = ok("#lang policylang 2\nentity E { @key id: Int [min: 1, max: 5], v: Bool }\n");
        assert!(s.entities[0].fields[0].is_key);
        assert!(!s.entities[0].fields[1].is_key);
        assert_eq!(s.entities[0].key_field().unwrap().name, "id");
    }

    #[test]
    fn missing_header_is_error() {
        let d = parse_spec("entity E { a: Int }\n", None).unwrap_err();
        assert_eq!(d[0].code, E_BAD_HEADER);
    }

    #[test]
    fn waiver_requires_all_fields_and_independent_approver() {
        assert!(parse_spec(
            "#lang policylang 2\nwaiver W { target: R, owner: \"a\", approver: \"a\", expires: \"2030-01-01\", reason: \"x\" }\n",
            None
        )
        .is_err());
        assert!(parse_spec(
            "#lang policylang 2\nwaiver W { target: R, owner: \"a\", expires: \"2030-01-01\" }\n",
            None
        )
        .is_err());
    }

    #[test]
    fn ipv6_roundtrip() {
        assert_eq!(parse_ipv6("::1").unwrap(), 1);
        assert_eq!(parse_ipv6("::").unwrap(), 0);
        assert_eq!(format_ip(parse_ipv6("2001:db8::1").unwrap(), 128), "2001:db8:0:0:0:0:0:1");
        assert!(parse_ipv6("1:2:3:4:5:6:7:8:9").is_none());
    }
}
