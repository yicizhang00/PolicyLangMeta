//! 声明级守卫与正则子语言校验（`03 §3.3 W6/W9/W10/W12`、`§3.9 W11`、`§3.13 R_sub`、`04 §9`）。
//!
//! ## R_sub（正则子语言）
//! `matches_all` 只接受**正则可判定**的 PCRE 子集；`τ` 把它转译为 SMT-LIB `RegLan`
//! （`TH-6` 语言保持定理）。拒绝清单区分两类错误码（`03 §3.13.2`）：
//! - `E-REGEX-NONREGULAR`：反向引用、递归、条件、环视 —— **本质非正则**，不可转译；
//! - `E-REGEX-UNSUPPORTED`：锚点、`\b`、`\p{…}`、占有量词、内联标志 —— 可改写。

use std::collections::BTreeMap;

use policylang_ast::codes::*;
use policylang_ast::diag::Diagnostic;
use policylang_ast::formula::{Expr, ExprKind, Formula, FormulaKind, RegLan};
use policylang_ast::naming;
use policylang_ast::spec::{PolicyDecl, Spec, VerifyKind, VerifyDecl};
use policylang_ast::Span;

use crate::budget::{measure_formula, GroundMeasure};
use crate::symbol_table::SymbolTable;
use crate::CheckOptions;

// ═════════════════════════════════════════════════════════════════════════════
// R_sub：解析与 τ 转译
// ═════════════════════════════════════════════════════════════════════════════

/// 校验并转译一条 R_sub 模式（预算 `n·|τ(r)| ≤ budget`）。
pub fn validate_r_sub(pattern: &str, span: Span, budget: u64) -> Result<RegLan, Diagnostic> {
    let r = parse_r_sub(pattern, span)?;
    let cost = r.size();
    if cost > budget {
        return Err(Diagnostic::error(
            E_REGEX_BUDGET,
            format!(
                "正则 `{pattern}` 的转译规模 |τ(r)| = {cost} 超出预算 {budget}（E-REGEX-BUDGET）"
            ),
        )
        .with_span(span));
    }
    Ok(r)
}

fn nonreg(pattern: &str, span: Span, why: &str) -> Diagnostic {
    Diagnostic::error(
        E_REGEX_NONREGULAR,
        format!("正则 `{pattern}` 含本质非正则构造：{why}（R_sub 拒绝清单，03 §3.13.2）"),
    )
    .with_span(span)
}

fn unsupported(pattern: &str, span: Span, why: &str, advice: &str) -> Diagnostic {
    Diagnostic::error(
        E_REGEX_UNSUPPORTED,
        format!("正则 `{pattern}` 含不支持的构造：{why}；{advice}"),
    )
    .with_span(span)
}

/// 把 R_sub 模式解析为 `RegLan`（`τ` 映射，`03 §3.13.1`）。
pub fn parse_r_sub(pattern: &str, span: Span) -> Result<RegLan, Diagnostic> {
    let chars: Vec<char> = pattern.chars().collect();
    let mut p = RSubParser {
        src: pattern,
        chars,
        pos: 0,
        span,
    };
    let r = p.parse_alt()?;
    if p.pos != p.chars.len() {
        return Err(Diagnostic::error(
            E_REGEX_UNSUPPORTED,
            format!(
                "正则 `{pattern}` 在偏移 {} 处有未解析字符 `{}`",
                p.pos, p.chars[p.pos]
            ),
        )
        .with_span(span));
    }
    Ok(r)
}

struct RSubParser<'a> {
    src: &'a str,
    chars: Vec<char>,
    pos: usize,
    span: Span,
}

impl RSubParser<'_> {
    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn next(&mut self) -> Option<char> {
        let c = self.chars.get(self.pos).copied();
        if c.is_some() {
            self.pos += 1;
        }
        c
    }

    fn parse_alt(&mut self) -> Result<RegLan, Diagnostic> {
        let mut branches = vec![self.parse_concat()?];
        while self.peek() == Some('|') {
            self.next();
            branches.push(self.parse_concat()?);
        }
        Ok(if branches.len() == 1 {
            branches.pop().unwrap()
        } else {
            RegLan::Union(branches)
        })
    }

    fn parse_concat(&mut self) -> Result<RegLan, Diagnostic> {
        let mut items: Vec<RegLan> = Vec::new();
        while let Some(c) = self.peek() {
            if c == '|' || c == ')' {
                break;
            }
            let atom = self.parse_repeat()?;
            items.push(atom);
        }
        Ok(RegLan::Concat(items))
    }

    fn parse_repeat(&mut self) -> Result<RegLan, Diagnostic> {
        let atom = self.parse_atom()?;
        // 占有量词 `*+` / `++` / `?+` → 不支持
        match self.peek() {
            Some('*') => {
                self.next();
                self.no_possessive()?;
                Ok(RegLan::Star(Box::new(atom)))
            }
            Some('+') => {
                self.next();
                self.no_possessive()?;
                Ok(RegLan::Plus(Box::new(atom)))
            }
            Some('?') => {
                self.next();
                self.no_possessive()?;
                Ok(RegLan::Opt(Box::new(atom)))
            }
            Some('{') => {
                let save = self.pos;
                self.next();
                let m = self.parse_uint();
                match (m, self.peek()) {
                    (Some(m), Some('}')) => {
                        self.next();
                        self.no_possessive()?;
                        Ok(RegLan::Loop(Box::new(atom), m, Some(m)))
                    }
                    (Some(m), Some(',')) => {
                        self.next();
                        let n = self.parse_uint();
                        if self.peek() != Some('}') {
                            return Err(unsupported(
                                self.src,
                                self.span,
                                "量词 `{m,` 缺少 `}`",
                                "请写成 `{m}`、`{m,n}` 或 `{m,}`",
                            ));
                        }
                        self.next();
                        self.no_possessive()?;
                        Ok(RegLan::Loop(Box::new(atom), m, n))
                    }
                    _ => {
                        self.pos = save;
                        Ok(atom)
                    }
                }
            }
            _ => Ok(atom),
        }
    }

    fn no_possessive(&mut self) -> Result<(), Diagnostic> {
        if self.peek() == Some('+') {
            return Err(unsupported(
                self.src,
                self.span,
                "占有量词（`*+` / `++` / `?+` / `{m,n}+`）",
                "请改用贪婪量词",
            ));
        }
        Ok(())
    }

    fn parse_uint(&mut self) -> Option<u32> {
        let start = self.pos;
        while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
            self.next();
        }
        if self.pos == start {
            return None;
        }
        self.chars[start..self.pos]
            .iter()
            .collect::<String>()
            .parse()
            .ok()
    }

    fn parse_atom(&mut self) -> Result<RegLan, Diagnostic> {
        match self.peek() {
            None => Ok(RegLan::Concat(vec![])), // ε
            Some('.') => {
                self.next();
                Ok(RegLan::AllChar)
            }
            Some('(') => {
                self.next();
                if self.peek() == Some('?') {
                    self.next();
                    match self.peek() {
                        Some(':') => {
                            self.next();
                        }
                        Some('=') | Some('!') => {
                            return Err(nonreg(self.src, self.span, "环视断言 `(?=` / `(?!`"));
                        }
                        Some('<') => {
                            self.next();
                            match self.peek() {
                                Some('=') | Some('!') => {
                                    return Err(nonreg(self.src, self.span, "环视断言 `(?<=` / `(?<!`"));
                                }
                                _ => {
                                    // `(?<name>…)` 具名捕获组：语义等同普通组，跳过名字
                                    while let Some(c) = self.peek() {
                                        if c == '>' {
                                            self.next();
                                            break;
                                        }
                                        self.next();
                                    }
                                }
                            }
                        }
                        Some('P') => {
                            self.next();
                            if self.peek() == Some('<') {
                                while let Some(c) = self.peek() {
                                    if c == '>' {
                                        self.next();
                                        break;
                                    }
                                    self.next();
                                }
                            } else {
                                return Err(unsupported(
                                    self.src,
                                    self.span,
                                    "`(?P…)` 的非具名形式",
                                    "请使用 `(?P<name>…)` 或普通组",
                                ));
                            }
                        }
                        Some('>') => {
                            return Err(unsupported(
                                self.src,
                                self.span,
                                "原子组 `(?>…)`",
                                "请改写为普通组",
                            ));
                        }
                        Some('R') | Some('0') | Some('&') => {
                            return Err(nonreg(self.src, self.span, "递归引用"));
                        }
                        Some('(') => {
                            return Err(nonreg(self.src, self.span, "条件组 `(?(…)…)`"));
                        }
                        Some(c) if c.is_ascii_alphabetic() => {
                            return Err(unsupported(
                                self.src,
                                self.span,
                                &format!("内联标志 `(?{c}…)`"),
                                "标志会改变语言语义，请显式改写模式",
                            ));
                        }
                        _ => {
                            return Err(unsupported(
                                self.src,
                                self.span,
                                "未知的 `(?…)` 组",
                                "请使用 `(?:…)`",
                            ));
                        }
                    }
                }
                let inner = self.parse_alt()?;
                if self.peek() != Some(')') {
                    return Err(unsupported(
                        self.src,
                        self.span,
                        "分组缺少 `)`",
                        "请补全括号",
                    ));
                }
                self.next();
                Ok(inner)
            }
            Some('[') => self.parse_class(),
            Some('\\') => self.parse_escape(),
            Some('^') | Some('$') => {
                self.next();
                Err(unsupported(
                    self.src,
                    self.span,
                    "锚点 `^` / `$`",
                    "`matches_all` 已是整串匹配语义，锚点冗余",
                ))
            }
            Some('*') | Some('+') | Some('?') => {
                let c = self.next().unwrap();
                Err(unsupported(
                    self.src,
                    self.span,
                    &format!("量词 `{c}` 没有前置原子"),
                    "请检查模式",
                ))
            }
            Some(c) => {
                self.next();
                Ok(RegLan::Str(c.to_string()))
            }
        }
    }

    fn parse_class(&mut self) -> Result<RegLan, Diagnostic> {
        self.next(); // '['
        let negated = if self.peek() == Some('^') {
            self.next();
            true
        } else {
            false
        };
        let mut alts: Vec<RegLan> = Vec::new();
        loop {
            match self.peek() {
                None => {
                    return Err(unsupported(
                        self.src,
                        self.span,
                        "字符类缺少 `]`",
                        "请补全",
                    ))
                }
                // `]` 直接结束字符类 ⇒ `[]` / `[^]` 落入下方「空字符类」判定
                Some(']') => {
                    self.next();
                    break;
                }
                _ => {}
            }
            let lo = self.parse_class_char(&mut alts)?;
            if self.peek() == Some('-') && self.chars.get(self.pos + 1).copied() != Some(']') {
                self.next();
                let hi = self.parse_class_char(&mut alts)?;
                let (Some(a), Some(b)) = (lo, hi) else {
                    return Err(unsupported(
                        self.src,
                        self.span,
                        "字符类区间端点必须是单个字符",
                        "请展开为多个区间",
                    ));
                };
                if a > b {
                    return Err(unsupported(
                        self.src,
                        self.span,
                        &format!("字符类区间 `{a}-{b}` 端点逆序"),
                        "请调整顺序",
                    ));
                }
                alts.push(RegLan::Range(a, b));
            } else if let Some(a) = lo {
                alts.push(RegLan::Str(a.to_string()));
            }
        }
        if alts.is_empty() {
            return Err(Diagnostic::error(
                E_REGEX_EMPTY_CLASS,
                format!("正则 `{}` 含空字符类（03 §3.13.2）", self.src),
            )
            .with_span(self.span));
        }
        let union = if alts.len() == 1 {
            alts.pop().unwrap()
        } else {
            RegLan::Union(alts)
        };
        Ok(if negated {
            RegLan::Complement(Box::new(union))
        } else {
            union
        })
    }

    /// 返回 `Some(c)` 表示单字符；`None` 表示已把（多字符）子语言压入 `alts`。
    fn parse_class_char(&mut self, alts: &mut Vec<RegLan>) -> Result<Option<char>, Diagnostic> {
        match self.peek() {
            Some('\\') => {
                let r = self.parse_escape()?;
                match r {
                    RegLan::Str(s) if s.chars().count() == 1 => {
                        Ok(Some(s.chars().next().unwrap()))
                    }
                    other => {
                        alts.push(other);
                        Ok(None)
                    }
                }
            }
            Some(c) => {
                self.next();
                Ok(Some(c))
            }
            None => Ok(None),
        }
    }

    fn parse_escape(&mut self) -> Result<RegLan, Diagnostic> {
        self.next(); // '\'
        let c = self.peek().ok_or_else(|| {
            unsupported(self.src, self.span, "模式以孤立 `\\` 结尾", "请补全转义")
        })?;
        self.next();
        match c {
            '1'..='9' => Err(nonreg(
                self.src,
                self.span,
                &format!("反向引用 `\\{c}`"),
            )),
            'k' | 'g' => Err(nonreg(self.src, self.span, "具名反向引用")),
            'b' | 'B' => Err(unsupported(
                self.src,
                self.span,
                &format!("`\\{c}` 词边界"),
                "请用显式字符类表达边界",
            )),
            'A' | 'z' | 'Z' | 'G' => Err(unsupported(
                self.src,
                self.span,
                &format!("`\\{c}` 锚点"),
                "整串匹配语义下锚点冗余",
            )),
            'p' | 'P' => Err(unsupported(
                self.src,
                self.span,
                &format!("`\\{c}{{…}}` Unicode 属性类"),
                "请改写为显式 `re.range` 区间",
            )),
            'X' | 'R' | 'C' | 'K' => Err(unsupported(
                self.src,
                self.span,
                &format!("`\\{c}`"),
                "请改写为受支持的构造",
            )),
            'd' => Ok(digit_class()),
            'D' => Ok(RegLan::Complement(Box::new(digit_class()))),
            'w' => Ok(word_class()),
            'W' => Ok(RegLan::Complement(Box::new(word_class()))),
            's' => Ok(space_class()),
            'S' => Ok(RegLan::Complement(Box::new(space_class()))),
            'n' => Ok(RegLan::Str("\n".into())),
            't' => Ok(RegLan::Str("\t".into())),
            'r' => Ok(RegLan::Str("\r".into())),
            other => Ok(RegLan::Str(other.to_string())),
        }
    }
}

fn digit_class() -> RegLan {
    RegLan::Range('0', '9')
}

fn word_class() -> RegLan {
    RegLan::Union(vec![
        RegLan::Range('A', 'Z'),
        RegLan::Range('a', 'z'),
        RegLan::Range('0', '9'),
        RegLan::Str("_".into()),
    ])
}

fn space_class() -> RegLan {
    RegLan::Union(vec![
        RegLan::Str(" ".into()),
        RegLan::Str("\t".into()),
        RegLan::Str("\n".into()),
        RegLan::Str("\r".into()),
    ])
}

/// 把多条模式转译为 `(re.inter …)`（`matches_all` 的语义，`TH-6-C1`）。
pub fn matches_all_reglan(patterns: &[String]) -> RegLan {
    RegLan::Inter(patterns.iter().map(|p| parse_r_sub(p, Span::default()).unwrap_or(RegLan::Empty)).collect())
}

// ═════════════════════════════════════════════════════════════════════════════
// 声明级守卫
// ═════════════════════════════════════════════════════════════════════════════

/// `W6` / `W12` / 分支与互斥预算。
pub fn check_policy_shape(
    p: &PolicyDecl,
    opts: &CheckOptions,
    diags: &mut Vec<Diagnostic>,
) {
    use std::collections::BTreeSet;
    let mut names: BTreeSet<&str> = BTreeSet::new();
    for r in &p.rules {
        if !names.insert(r.name.as_str()) {
            diags.push(
                Diagnostic::error(
                    E_DUP_NAME,
                    format!("策略 `{}` 中 `rule {}` 名称重复（W6）", p.name, r.name),
                )
                .with_span(r.span),
            );
        }
    }
    let mut bnames: BTreeSet<&str> = BTreeSet::new();
    for b in &p.branches {
        if !bnames.insert(b.name.as_str()) {
            diags.push(
                Diagnostic::error(
                    E_DUP_NAME,
                    format!("策略 `{}` 中 `branch {}` 名称重复（W6）", p.name, b.name),
                )
                .with_span(b.span),
            );
        }
    }
    if p.rules.is_empty() {
        diags.push(
            Diagnostic::error(
                E_EMPTYPOLICY,
                format!("策略 `{}` 不含任何 `rule`：空策略使 `consistency` 空真（W12）", p.name),
            )
            .with_span(p.span),
        );
    }
    for m in &p.mutexes {
        for n in &m.names {
            if !bnames.contains(n.as_str()) {
                diags.push(
                    Diagnostic::error(
                        E_MUTEX_UNKNOWN_BRANCH,
                        format!("`mutex` 引用了策略 `{}` 中不存在的分支 `{n}`", p.name),
                    )
                    .with_span(m.span),
                );
            }
        }
    }
    let pairs = branch_pairs(&p.branches);
    if pairs > opts.mutex_max_pairs {
        diags.push(
            Diagnostic::error(
                E_MUTEX_BUDGET,
                format!(
                    "策略 `{}` 的分支对数 C(k,2) = {pairs} 超出 `--mutex-max-pairs` = {}；\
                     建议先合并分支（06 §6.3.6）",
                    p.name, opts.mutex_max_pairs
                ),
            )
            .with_span(p.span),
        );
    }
}

/// 分支对数 `C(k, 2)`。
pub fn branch_pairs(branches: &[policylang_ast::spec::BranchDecl]) -> usize {
    let k = branches.len();
    k.saturating_sub(1) * k / 2
}

/// `verify` 的引用与前置条件校验。
pub fn check_verify(v: &VerifyDecl, tab: &SymbolTable, diags: &mut Vec<Diagnostic>) {
    let need_policy = |tab: &SymbolTable, name: &str, diags: &mut Vec<Diagnostic>| {
        if !tab.policies.contains_key(name) {
            diags.push(
                Diagnostic::error(
                    E_VERIFY_UNKNOWN,
                    format!("`verify` 引用了未声明的策略 `{name}`"),
                )
                .with_span(v.span),
            );
            return false;
        }
        true
    };
    let need_branches = |tab: &SymbolTable, name: &str, diags: &mut Vec<Diagnostic>| {
        match tab.policies.get(name) {
            Some(p) if !p.branches.is_empty() => true,
            Some(_) => {
                diags.push(
                    Diagnostic::error(
                        E_NO_BRANCHES,
                        format!(
                            "策略 `{name}` 无 `branch` 声明，无法执行该目标（06 §6.3.4：E-NO-BRANCHES）"
                        ),
                    )
                    .with_span(v.span),
                );
                false
            }
            None => false,
        }
    };
    match &v.kind {
        VerifyKind::Consistency { policy } => {
            need_policy(tab, policy, diags);
        }
        VerifyKind::Safety { policy } => {
            need_policy(tab, policy, diags);
        }
        VerifyKind::Completeness { policy } => {
            if need_policy(tab, policy, diags) {
                need_branches(tab, policy, diags);
            }
        }
        VerifyKind::Mutex { policy } => {
            if need_policy(tab, policy, diags) {
                need_branches(tab, policy, diags);
            }
        }
        VerifyKind::Refines {
            new_policy,
            old_policy,
        } => {
            need_policy(tab, new_policy, diags);
            need_policy(tab, old_policy, diags);
        }
        VerifyKind::Invariant { invariant, policy } => {
            need_policy(tab, policy, diags);
            if !tab.invariants.contains_key(invariant) {
                diags.push(
                    Diagnostic::error(
                        E_VERIFY_UNKNOWN,
                        format!("`verify invariant` 引用了未声明的不变量 `{invariant}`"),
                    )
                    .with_span(v.span),
                );
            }
        }
    }
}

/// `W11`：对全部验证目标涉及公式做展开预算检查。
///
/// 返回 `(目标名, 度量)` 的有序映射（保序 ⇒ 可复算）。
pub fn check_budget(
    spec: &Spec,
    tab: &SymbolTable,
    opts: &CheckOptions,
    diags: &mut Vec<Diagnostic>,
) -> BTreeMap<String, GroundMeasure> {
    let _ = tab; // 预算仅依赖域规模，符号表由调用方先行校验
    let sizes = crate::budget::domain_sizes(spec);
    let cap = opts.max_groundings as u128;
    let mut out: BTreeMap<String, GroundMeasure> = BTreeMap::new();

    let mut check_one = |name: String, forms: Vec<&Formula>, diags: &mut Vec<Diagnostic>| {
        let mut total = 0u128;
        let mut before = 0u128;
        let mut ovf = false;
        for f in forms {
            let m = measure_formula(f, &sizes, cap);
            total = total.saturating_add(m.atoms_after).min(u128::MAX);
            before = before.saturating_add(m.atoms_before);
            ovf |= m.overflow;
        }
        let measure = GroundMeasure {
            atoms_before: before,
            atoms_after: total.min(cap),
            overflow: ovf,
        };
        if measure.overflow || measure.atoms_after >= cap {
            diags.push(
                Diagnostic::error(
                    E_GROUNDING_BUDGET,
                    format!(
                        "`{name}` 的展开规模 G(φ) ≥ {} 超出预算 G_max = {cap}（W11 / E-GROUNDING-BUDGET）；\
                         请减小域 `size`、减少量词绑定变量数，或使用 `distinct` 降阶（03 §3.9）",
                        measure.atoms_after
                    ),
                ),
            );
        }
        out.insert(name, measure);
    };

    for p in &spec.policies {
        let forms: Vec<&Formula> = p.rules.iter().map(|r| &r.formula).collect();
        check_one(format!("{}::consistency", p.name), forms, diags);
        let bforms: Vec<&Formula> = p.branches.iter().map(|b| &b.formula).collect();
        check_one(format!("{}::completeness", p.name), bforms, diags);
    }
    for i in &spec.invariants {
        check_one(format!("invariant::{}", i.name), vec![&i.formula], diags);
    }
    for r in &spec.requires {
        check_one(format!("require::{}", r.name), vec![&r.formula], diags);
    }
    out
}

// ═════════════════════════════════════════════════════════════════════════════
// :named 标签表（NM-3）与唯一性（E-DUP-LABEL）
// ═════════════════════════════════════════════════════════════════════════════

/// 标签用途分类（供 `07 §7.3` 的归因使用）。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LabelKind {
    Rule,
    Branch,
    InvariantNeg,
    Mutex,
    CompletenessNeg,
    SafetyDivZero,
    OldNeg,
}

/// 标签 → (用途, 归属名, 源码位置) 的有序表。
pub type LabelMap = BTreeMap<String, (LabelKind, String, Span)>;

/// 收集全部 `:named` 标签并检测冲突（`NM-3` 要求标签唯一，冲突即 `E-DUP-LABEL`）。
pub fn collect_labels(spec: &Spec) -> Result<LabelMap, Vec<Diagnostic>> {
    let mut map: LabelMap = BTreeMap::new();
    let mut diags: Vec<Diagnostic> = Vec::new();

    let put = |label: String,
                   kind: LabelKind,
                   owner: String,
                   span: Span,
                   map: &mut LabelMap,
                   diags: &mut Vec<Diagnostic>| {
        if let Some((_, prev, pspan)) = map.get(&label) {
            diags.push(
                Diagnostic::error(
                    E_DUP_LABEL,
                    format!(
                        "`:named` 标签 `{label}` 冲突：`{prev}`（{}:{}）与 `{owner}`（{}:{}）\
                         （NM-3 要求标签唯一）",
                        pspan.start_line, pspan.start_col, span.start_line, span.start_col
                    ),
                )
                .with_span(span),
            );
            return;
        }
        map.insert(label, (kind, owner, span));
    };

    for p in &spec.policies {
        for r in &p.rules {
            put(
                naming::label_rule(&p.name, &r.name),
                LabelKind::Rule,
                r.name.clone(),
                r.span,
                &mut map,
                &mut diags,
            );
        }
        for b in &p.branches {
            put(
                naming::label_branch(&p.name, &b.name),
                LabelKind::Branch,
                b.name.clone(),
                b.span,
                &mut map,
                &mut diags,
            );
        }
        put(
            naming::label_completeness(&p.name),
            LabelKind::CompletenessNeg,
            p.name.clone(),
            p.span,
            &mut map,
            &mut diags,
        );
        put(
            naming::label_safety_divzero(&p.name),
            LabelKind::SafetyDivZero,
            p.name.clone(),
            p.span,
            &mut map,
            &mut diags,
        );
        put(
            naming::label_old_neg(&p.name),
            LabelKind::OldNeg,
            p.name.clone(),
            p.span,
            &mut map,
            &mut diags,
        );
        let (i, j) = (0usize, 1usize);
        if p.branches.len() >= 2 {
            put(
                naming::label_mutex(&p.name, i, j),
                LabelKind::Mutex,
                p.name.clone(),
                p.span,
                &mut map,
                &mut diags,
            );
        }
    }
    for i in &spec.invariants {
        put(
            naming::label_invariant(&i.name),
            LabelKind::InvariantNeg,
            i.name.clone(),
            i.span,
            &mut map,
            &mut diags,
        );
    }

    if diags.iter().any(Diagnostic::is_error) {
        Err(diags)
    } else {
        Ok(map)
    }
}

/// 判断公式中是否出现除法（用于 `ALG-2` 与 `safety` 的空真判定）。
pub fn contains_division(f: &Formula) -> bool {
    fn in_expr(e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Arith { op, lhs, rhs } => {
                op.is_div_like() || in_expr(lhs) || in_expr(rhs)
            }
            ExprKind::Neg(a) | ExprKind::StrLen(a) | ExprKind::ToReal(a) | ExprKind::Bv2Int(a) => {
                in_expr(a)
            }
            ExprKind::Int2Bv { value, .. } => in_expr(value),
            ExprKind::Bv { lhs, rhs, .. } => in_expr(lhs) || in_expr(rhs),
            _ => false,
        }
    }
    match &f.kind {
        FormulaKind::Atom(a) => match a {
            policylang_ast::formula::Atom::Cmp { lhs, rhs, .. } => {
                in_expr(lhs) || in_expr(rhs)
            }
            policylang_ast::formula::Atom::Bool(e) => in_expr(e),
        },
        FormulaKind::Not(x) => contains_division(x),
        FormulaKind::And(v) | FormulaKind::Or(v) => v.iter().any(contains_division),
        FormulaKind::Implies(a, b) | FormulaKind::Iff(a, b) => {
            contains_division(a) || contains_division(b)
        }
        FormulaKind::Forall { body, .. } | FormulaKind::Exists { body, .. } => {
            contains_division(body)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use policylang_ast::Spec;

    fn sp() -> Span {
        Span::new(1, 1, 1, 2)
    }

    #[test]
    fn translates_supported_patterns() {
        let r = parse_r_sub(".*[A-Z].*", sp()).unwrap();
        assert_eq!(
            r.to_smt(),
            "(re.++ (re.* re.allchar) (re.range \"A\" \"Z\") (re.* re.allchar))"
        );
        assert!(parse_r_sub("[A-Z].*", sp()).is_ok());
        assert!(parse_r_sub("\\d{3}-\\d{4}", sp()).is_ok());
        assert!(parse_r_sub("(?:ab|cd)+", sp()).is_ok());
        assert!(parse_r_sub("[^0-9]", sp()).is_ok());
        assert!(parse_r_sub("\\w+@\\w+", sp()).is_ok());
    }

    #[test]
    fn rejects_nonregular_constructs() {
        for (pat, code) in [
            ("(a)\\1", E_REGEX_NONREGULAR),
            ("(?=abc)", E_REGEX_NONREGULAR),
            ("(?<=abc)x", E_REGEX_NONREGULAR),
            ("(?R)", E_REGEX_NONREGULAR),
            ("(?(1)a|b)", E_REGEX_NONREGULAR),
            ("\\bword\\b", E_REGEX_UNSUPPORTED),
            ("^abc$", E_REGEX_UNSUPPORTED),
            ("a*+", E_REGEX_UNSUPPORTED),
            ("(?i)abc", E_REGEX_UNSUPPORTED),
            ("\\p{L}+", E_REGEX_UNSUPPORTED),
            ("(?>abc)", E_REGEX_UNSUPPORTED),
            ("[]", E_REGEX_EMPTY_CLASS),
        ] {
            let e = parse_r_sub(pat, sp()).unwrap_err();
            assert_eq!(e.code, code, "模式 `{pat}` 的错误码应为 {code}，实际 {}", e.code);
        }
    }

    #[test]
    fn budget_is_enforced() {
        let long = "a".repeat(100);
        assert!(validate_r_sub(&long, sp(), 4096).is_ok());
        assert_eq!(
            validate_r_sub(&long, sp(), 10).unwrap_err().code,
            E_REGEX_BUDGET
        );
    }

    #[test]
    fn matches_all_is_inter() {
        let r = matches_all_reglan(&[".*[A-Z].*".into(), ".*[0-9].*".into()]);
        assert!(r.to_smt().starts_with("(re.inter "));
    }

    #[test]
    fn division_detection() {
        let s: Spec = crate::testutil::spec_of("var a: Int\nvar b: Int\nrequire R: a / b > 1\n");
        assert!(contains_division(&s.requires[0].formula));
        let s2: Spec = crate::testutil::spec_of("var a: Int\nrequire R: a > 1\n");
        assert!(!contains_division(&s2.requires[0].formula));
    }
}
