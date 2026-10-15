//! 类型检查、作用域检查与可判定性守卫 `W3`/`W5`/`W7`/`W8`（`03 §3.3`、`§3.4`、`05 §5`）。
//!
//! 本模块在一次遍历中同时完成：
//! 1. **排序推断**（`03 §3.4.2` 类型规则）；
//! 2. **作用域检查**（`D-2`：字段访问必须落在绑定变量所绑定的域上）；
//! 3. **可判定性守卫**（`W8`：`LinMul` 与除法侧条件，修正 `C-5`/`A-12`）；
//! 4. **理论足迹累加**（`06 §6.4.1` 的排序驱动置位）。
//!
//! 一次遍历同时产出这四项，避免「校验一处、置位另一处」的漂移（`B-7` 的根因）。

use std::collections::BTreeSet;

use policylang_ast::codes::*;
use policylang_ast::diag::Diagnostic;
use policylang_ast::formula::{ArithOp, Atom, CmpOp, Expr, ExprKind, Formula, FormulaKind, Sort};
use policylang_ast::spec::{LogicProfile, RangeConstraint, Spec};
use policylang_ast::Span;

use crate::logic_profile as lp;
use crate::symbol_table::{cross_domain_hint, Binding, Scope, SymbolTable};
use crate::{guardian, CheckOptions};

/// 公式检查器（携带作用域、足迹与诊断）。
pub struct FormulaChecker<'a> {
    tab: &'a SymbolTable,
    opts: &'a CheckOptions,
    scope: Scope,
    /// 全部声明中出现过的 `Enum` 排序（用于把裸标识符识别为枚举成员）。
    enum_sorts: Vec<Sort>,
    profile: LogicProfile,
    diags: Vec<Diagnostic>,
}

impl<'a> FormulaChecker<'a> {
    pub fn new(tab: &'a SymbolTable, opts: &'a CheckOptions, spec: &Spec) -> Self {
        let mut enum_sorts: Vec<Sort> = Vec::new();
        for e in &spec.entities {
            for f in &e.fields {
                if matches!(f.sort, Sort::Enum(_)) {
                    enum_sorts.push(f.sort.clone());
                }
            }
        }
        for v in &spec.vars {
            if matches!(v.sort, Sort::Enum(_)) {
                enum_sorts.push(v.sort.clone());
            }
        }
        FormulaChecker {
            tab,
            opts,
            scope: Scope::new(),
            enum_sorts,
            profile: LogicProfile::default(),
            diags: Vec::new(),
        }
    }

    /// 取走足迹与诊断。
    pub fn finish(self) -> (LogicProfile, Vec<Diagnostic>) {
        (self.profile, self.diags)
    }

    pub fn profile_ref(&self) -> &LogicProfile {
        &self.profile
    }

    fn err(&mut self, code: &str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::error(code, msg).with_span(span));
    }

    fn warn(&mut self, code: &str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::warning(code, msg).with_span(span));
    }

    // ─────────────────────────────────────────────────────────────────────────
    // 公式
    // ─────────────────────────────────────────────────────────────────────────

    /// 检查公式并断言其排序为 `Bool`（`W7`）。
    pub fn check(&mut self, f: &Formula) -> bool {
        match &f.kind {
            FormulaKind::True | FormulaKind::False => true,
            FormulaKind::Atom(a) => self.check_atom(a, f.span),
            FormulaKind::Not(x) => self.check(x),
            FormulaKind::And(v) | FormulaKind::Or(v) => {
                let mut ok = true;
                for x in v {
                    ok &= self.check(x);
                }
                ok
            }
            FormulaKind::Implies(a, b) | FormulaKind::Iff(a, b) => {
                let x = self.check(a);
                let y = self.check(b);
                x && y
            }
            FormulaKind::Forall {
                vars,
                domain,
                distinct,
                body,
            }
            | FormulaKind::Exists {
                vars,
                domain,
                distinct,
                body,
            } => {
                let _ = distinct;
                self.check_quantifier(vars, domain, body, f.span)
            }
            FormulaKind::MatchesAll { subject, patterns } => {
                let ok = self.expect_sort(subject, &Sort::Str, "matches_all 的被匹配表达式");
                lp::mark_regex(&mut self.profile);
                let mut all = ok;
                for p in patterns {
                    match guardian::validate_r_sub(p, f.span, self.opts.regex_budget) {
                        Ok(_) => {}
                        Err(d) => {
                            self.diags.push(d);
                            all = false;
                        }
                    }
                }
                if patterns.is_empty() {
                    // `matches_all []` ⇒ 恒真（⋀∅ = ⊤ 的对偶）；显式告警以免静默。
                    self.warn(
                        W_VACUOUS_SAFETY,
                        "`matches_all []` 为空模式列表，按 `⋀∅ = ⊤` 恒真（03 §3.5.3）",
                        f.span,
                    );
                }
                all
            }
            FormulaKind::InCidr { subject, cidr } => {
                self.check_linear_free(subject);
                let want = Sort::Bv(cidr.width);
                let ok = self.expect_sort(subject, &want, "in_cidr 的被检查表达式");
                lp::mark_sort(&mut self.profile, &want);
                ok
            }
            FormulaKind::InRange {
                subject,
                width,
                lo,
                hi,
                ..
            } => {
                self.check_linear_free(subject);
                let want = Sort::Bv(*width);
                let ok = self.expect_sort(subject, &want, "in_range 的被检查表达式");
                let _ = (lo, hi);
                lp::mark_sort(&mut self.profile, &want);
                ok
            }
            FormulaKind::Unique { domain, field } => {
                let Some(info) = self.tab.domains.get(domain) else {
                    self.err(
                        E_UNKNOWN_REF,
                        format!("`unique` 引用了未声明的域 `{domain}`"),
                        f.span,
                    );
                    return false;
                };
                let entity = info.entity.clone();
                let Some(ent) = self.tab.entities.get(&entity) else {
                    return false;
                };
                let Some(fd) = ent.fields.iter().find(|x| x.name == *field) else {
                    self.err(
                        E_UNKNOWN_REF,
                        format!("实体 `{entity}` 没有字段 `{field}`（`unique({domain}, {field})`）"),
                        f.span,
                    );
                    return false;
                };
                if !fd.sort.is_key_eligible() {
                    self.err(
                        E_SORT_MISMATCH,
                        format!(
                            "`unique({domain}, {field})` 的字段排序为 `{}`，不可唯一化\
                             （Real 不稳定、Bool 区分度不足，03 §3.4.2 T-UNIQUE）",
                            fd.sort.source_name()
                        ),
                        f.span,
                    );
                    return false;
                }
                lp::mark_sort(&mut self.profile, &fd.sort.clone());
                true
            }
        }
    }

    fn check_quantifier(
        &mut self,
        vars: &[String],
        domain: &str,
        body: &Formula,
        span: Span,
    ) -> bool {
        let Some(info) = self.tab.domains.get(domain) else {
            self.err(
                E_UNKNOWN_REF,
                format!("量词引用了未声明的域 `{domain}`"),
                span,
            );
            return false;
        };
        let (dname, entity) = (info.name.clone(), info.entity.clone());
        if vars.is_empty() {
            self.err(E_SYNTAX, "量词缺少绑定变量（W5）", span);
            return false;
        }
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        for v in vars {
            if !seen.insert(v.as_str()) {
                self.warn(
                    W_DUP_VAR,
                    format!("量词中变量 `{v}` 重复出现（W5）"),
                    span,
                );
            }
            if self.tab.vars.contains_key(v) {
                self.warn(
                    W_SHADOW,
                    format!("量化变量 `{v}` 遮蔽了同名全局变量（D-2）"),
                    span,
                );
            }
        }
        self.scope.push();
        for v in vars {
            self.scope.bind(
                v.clone(),
                Binding {
                    domain: dname.clone(),
                    entity: entity.clone(),
                    span,
                },
            );
        }
        let ok = self.check(body);
        self.scope.pop();
        ok
    }

    fn check_atom(&mut self, a: &Atom, span: Span) -> bool {
        match a {
            Atom::Bool(e) => {
                self.expect_sort(e, &Sort::Bool, "布尔原子（T-BOOL-ATOM）")
            }
            Atom::Cmp { lhs, op, rhs } => self.check_cmp(lhs, *op, rhs, span),
        }
    }

    fn check_cmp(&mut self, lhs: &Expr, op: CmpOp, rhs: &Expr, span: Span) -> bool {
        // ── W8 可判定性守卫（在与排序无关的独立通道上运行，保证即使排序有误也报出非线性）──
        let (lc, rc) = (lhs.is_constant(), rhs.is_constant());
        self.check_linear_side(lhs, rc);
        self.check_linear_side(rhs, lc);

        // ── 排序 ──
        let ls = self.expr_sort(lhs);
        let rs = self.expr_sort(rhs);
        let (Some(ls), Some(rs)) = (ls, rs) else {
            return false;
        };
        let (ls, rs) = self.unify_numeric(lhs, ls, rhs, rs);
        let both = |a: &Sort| ls == *a && rs == *a;

        let ok = match op {
            CmpOp::Eq | CmpOp::Ne => {
                if ls == rs {
                    true
                } else {
                    self.err(
                        E_SORT_MISMATCH,
                        format!(
                            "`{}` 两侧排序不一致：`{}` vs `{}`（N-4：禁止隐式提升，请显式 `to_real`）",
                            op.symbol(),
                            ls.source_name(),
                            rs.source_name()
                        ),
                        span,
                    );
                    false
                }
            }
            CmpOp::Lt | CmpOp::Le | CmpOp::Gt | CmpOp::Ge => match (&ls, &rs) {
                (Sort::Int, Sort::Int) | (Sort::Real, Sort::Real) => true,
                (Sort::Bv(a), Sort::Bv(b)) if a == b => true,
                _ => {
                    self.err(
                        E_SORT_MISMATCH,
                        format!(
                            "`{}` 需要同族的数值或同位宽的无符号位向量，实际 `{}` vs `{}`",
                            op.symbol(),
                            ls.source_name(),
                            rs.source_name()
                        ),
                        span,
                    );
                    false
                }
            },
            CmpOp::StrLt | CmpOp::StrLe => {
                if both(&Sort::Str) {
                    true
                } else {
                    self.err(
                        E_SORT_MISMATCH,
                        format!(
                            "`{}` 仅适用于 `String`，实际 `{}` vs `{}`",
                            op.symbol(),
                            ls.source_name(),
                            rs.source_name()
                        ),
                        span,
                    );
                    false
                }
            }
        };
        ok
    }

    /// 数值字面量的**字面量提升**规则：`Int` 字面量出现在 `Real` 语境时按 `Real` 处理
    /// （发射阶段补 `(to_real n)`）。变量/字段之间的提升仍被 `N-4` 禁止。
    fn unify_numeric(&self, le: &Expr, ls: Sort, re: &Expr, rs: Sort) -> (Sort, Sort) {
        let lit = |e: &Expr| matches!(e.kind, ExprKind::IntLit(_) | ExprKind::RealLit(_));
        match (&ls, &rs) {
            (Sort::Int, Sort::Real) if lit(le) => (Sort::Real, rs),
            (Sort::Real, Sort::Int) if lit(re) => (ls, Sort::Real),
            _ => (ls, rs),
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // 表达式排序
    // ─────────────────────────────────────────────────────────────────────────

    pub fn expr_sort(&mut self, e: &Expr) -> Option<Sort> {
        let s = self.expr_sort_inner(e)?;
        lp::mark_sort(&mut self.profile, &s);
        Some(s)
    }

    fn expr_sort_inner(&mut self, e: &Expr) -> Option<Sort> {
        match &e.kind {
            ExprKind::IntLit(_) => Some(Sort::Int),
            ExprKind::RealLit(_) => Some(Sort::Real),
            ExprKind::BoolLit(_) => Some(Sort::Bool),
            ExprKind::StrLit(_) => Some(Sort::Str),
            ExprKind::Var(name) => {
                if let Some(v) = self.tab.vars.get(name) {
                    return Some(v.sort.clone());
                }
                if self.scope.lookup(name).is_some() {
                    self.err(
                        E_SORT_MISMATCH,
                        format!("`{name}` 是域实例（非标量），请使用 `{name}.<字段>`（03 §3.4）"),
                        e.span,
                    );
                    return None;
                }
                // 枚举成员：`a.kyc_level == Institutional`
                let mut hits: Vec<Sort> = self
                    .enum_sorts
                    .iter()
                    .filter(|s| match s {
                        Sort::Enum(ms) => ms.iter().any(|m| m == name),
                        _ => false,
                    })
                    .cloned()
                    .collect();
                hits.dedup();
                match hits.len() {
                    0 => {
                        self.err(
                            E_UNKNOWN_REF,
                            format!("未声明的标识符 `{name}`（既非全局变量，也非枚举成员）"),
                            e.span,
                        );
                        None
                    }
                    1 => Some(hits.remove(0)),
                    _ => {
                        self.err(
                            E_SORT_MISMATCH,
                            format!("枚举成员 `{name}` 在多个 `Enum` 排序中出现，无法确定其排序，请显式限定"),
                            e.span,
                        );
                        None
                    }
                }
            }
            ExprKind::FieldAccess { instance, field } => {
                let Some(b) = self.scope.lookup(instance).cloned() else {
                    self.err(
                        E_UNKNOWN_REF,
                        format!("`{instance}` 不是当前作用域内的域绑定变量（D-2）"),
                        e.span,
                    );
                    return None;
                };
                let ent = self.tab.entities.get(&b.entity)?;
                match ent.fields.iter().find(|f| f.name == *field) {
                    Some(f) => Some(f.sort.clone()),
                    None => {
                        if let Some(other) = cross_domain_hint(&self.scope, self.tab, field) {
                            self.err(
                                E_CROSS_DOMAIN_REF,
                                format!(
                                    "字段 `{field}` 不属于域 `{}`（实体 `{}`）而属于 `{other}`；\
                                     跨域字段引用被 D-2 禁止",
                                    b.domain, b.entity
                                ),
                                e.span,
                            );
                        } else {
                            self.err(
                                E_UNKNOWN_REF,
                                format!("实体 `{}` 没有字段 `{field}`", b.entity),
                                e.span,
                            );
                        }
                        None
                    }
                }
            }
            ExprKind::Flat { domain, field, .. } => {
                let ent = self.tab.entity_of_domain(domain)?;
                ent.fields
                    .iter()
                    .find(|f| f.name == *field)
                    .map(|f| f.sort.clone())
            }
            ExprKind::Arith { op, lhs, rhs } => self.arith_sort(*op, lhs, rhs, e.span),
            ExprKind::Neg(a) => {
                let s = self.expr_sort(a)?;
                if s.is_numeric() {
                    Some(s)
                } else {
                    self.err(
                        E_SORT_MISMATCH,
                        format!("一元负号仅适用于数值，实际 `{}`", s.source_name()),
                        e.span,
                    );
                    None
                }
            }
            ExprKind::StrLen(a) => {
                let ok = self.expect_sort(a, &Sort::Str, "str.len 的参数");
                lp::mark_sort(&mut self.profile, &Sort::Int);
                if ok {
                    Some(Sort::Int)
                } else {
                    None
                }
            }
            ExprKind::ToReal(a) => {
                let s = self.expr_sort(a);
                lp::mark_to_real(&mut self.profile);
                match s {
                    Some(Sort::Int) => Some(Sort::Real),
                    Some(Sort::Real) => Some(Sort::Real),
                    Some(other) => {
                        self.err(
                            E_SORT_MISMATCH,
                            format!("`to_real` 仅接受 `Int`，实际 `{}`", other.source_name()),
                            e.span,
                        );
                        None
                    }
                    None => None,
                }
            }
            ExprKind::Int2Bv { width, value } => {
                let s = self.expr_sort(value)?;
                let bv = Sort::Bv(*width);
                lp::mark_sort(&mut self.profile, &bv);
                if s == Sort::Int {
                    Some(bv)
                } else {
                    self.err(
                        E_SORT_MISMATCH,
                        format!("`int2bv` 仅接受 `Int`，实际 `{}`", s.source_name()),
                        e.span,
                    );
                    None
                }
            }
            ExprKind::Bv2Int(a) => {
                self.check_linear_free(a);
                let _ = self.expr_sort(a);
                // `03 §3.2.3 N-4`：`bv2int` 会引入非线性（位向量 ↔ 整数），编译期拒绝。
                self.err(
                    E_NONLINEAR,
                    "`bv2int` 引入非线性（BV ↔ Int），与 G-4 的可判定性承诺冲突，编译期拒绝（03 §3.2.3 N-4）",
                    e.span,
                );
                None
            }
            ExprKind::Bv {
                op, lhs, rhs, ..
            } => {
                self.check_linear_free(lhs);
                if !op.is_unary() {
                    self.check_linear_free(rhs);
                }
                let ls = self.expr_sort(lhs)?;
                let rs = if op.is_unary() {
                    ls.clone()
                } else {
                    self.expr_sort(rhs)?
                };
                match (&ls, &rs) {
                    (Sort::Bv(a), Sort::Bv(b)) if a == b => {
                        lp::mark_sort(&mut self.profile, &ls);
                        Some(ls)
                    }
                    _ => {
                        self.err(
                            E_SORT_MISMATCH,
                            format!(
                                "位向量运算 `{}` 需要两个同宽 `BitVec`，实际 `{}` vs `{}`",
                                op.smt_name(),
                                ls.source_name(),
                                rs.source_name()
                            ),
                            e.span,
                        );
                        None
                    }
                }
            }
        }
    }

    fn arith_sort(&mut self, op: ArithOp, lhs: &Expr, rhs: &Expr, span: Span) -> Option<Sort> {
        let ls = self.expr_sort(lhs)?;
        let rs = self.expr_sort(rhs)?;
        let (ls, rs) = self.unify_numeric(lhs, ls, rhs, rs);
        let mismatch = |me: &mut Self| {
            me.err(
                E_SORT_MISMATCH,
                format!(
                    "算术 `{}` 两侧排序不一致：`{}` vs `{}`（N-4：禁止隐式提升）",
                    op.symbol(),
                    ls.source_name(),
                    rs.source_name()
                ),
                span,
            );
            None::<Sort>
        };
        match arith_rule(op, &ls, &rs) {
            Some(s) => Some(s),
            None => mismatch(self),
        }
    }

    /// 断言表达式排序等于 `want`（必要时允许 `Int` 字面量提升到 `Real`）。
    fn expect_sort(&mut self, e: &Expr, want: &Sort, what: &str) -> bool {
        let Some(got) = self.expr_sort(e) else {
            return false;
        };
        if got == *want {
            return true;
        }
        if *want == Sort::Real && got == Sort::Int && matches!(e.kind, ExprKind::IntLit(_)) {
            return true;
        }
        self.err(
            E_SORT_MISMATCH,
            format!(
                "{what} 需要 `{}`，实际 `{}`（W7 / T-BOOL-ATOM）",
                want.source_name(),
                got.source_name()
            ),
            e.span,
        );
        false
    }

    // ─────────────────────────────────────────────────────────────────────────
    // W8 可判定性守卫
    // ─────────────────────────────────────────────────────────────────────────

    /// 在没有比较上下文的位置检查线性性（除数为非常量即违规）。
    fn check_linear_free(&mut self, e: &Expr) {
        self.check_linear_side(e, false);
    }

    /// `W8`：线性性侧条件（修正 `C-5`：**乘 / 除两个独立侧条件**）。
    ///
    /// - 乘法：`LinMul(a,b) ≜ isConst(a) ∨ isConst(b)`；
    /// - `/`：除数可常量，或满足 `LinDiv`（比较另一侧为常量 ⇒ 交叉相乘保持线性）；
    /// - `div`/`mod`：除数**必须**为常量。
    fn check_linear_side(&mut self, e: &Expr, other_is_const: bool) {
        match &e.kind {
            ExprKind::Arith { op, lhs, rhs } => {
                match op {
                    ArithOp::Mul => {
                        if !lhs.is_constant() && !rhs.is_constant() {
                            self.nonlinear(
                                &format!(
                                    "`{} * {}`：乘法两侧皆非常量（LinMul 不成立）",
                                    describe(lhs),
                                    describe(rhs)
                                ),
                                e.span,
                            );
                        }
                    }
                    ArithOp::RealDiv => {
                        if let Some(c) = rhs.as_num_lit() {
                            if c.is_zero() {
                                self.err(
                                    E_DIV_ZERO_CONST,
                                    "除数为字面量 0：除法在 0 处取值未指定（A-12），编译期拒绝",
                                    e.span,
                                );
                            }
                        } else if !other_is_const {
                            self.nonlinear(
                                &format!(
                                    "`{} / {}`：除数非常量且比较另一侧亦非常量 ⇒ LinDiv 不成立（03 §3.11.3）",
                                    describe(lhs),
                                    describe(rhs)
                                ),
                                e.span,
                            );
                        }
                    }
                    ArithOp::IntDiv | ArithOp::IntMod => match rhs.as_num_lit() {
                        Some(c) if c.is_zero() => self.err(
                            E_DIV_ZERO_CONST,
                            format!("`{}` 的除数为字面量 0", op.symbol()),
                            e.span,
                        ),
                        Some(_) => lp::mark_div_const(&mut self.profile, *op == ArithOp::IntMod),
                        None => self.nonlinear(
                            &format!(
                                "`{}` 的除数 `{}` 非常量（div/mod 要求常量除数，03 §3.4.1）",
                                op.symbol(),
                                describe(rhs)
                            ),
                            e.span,
                        ),
                    },
                    ArithOp::Add | ArithOp::Sub => {}
                }
                self.check_linear_side(lhs, false);
                self.check_linear_side(rhs, false);
            }
            ExprKind::Neg(a) | ExprKind::ToReal(a) | ExprKind::Bv2Int(a) => {
                self.check_linear_side(a, false)
            }
            ExprKind::StrLen(a) => self.check_linear_side(a, false),
            ExprKind::Int2Bv { value, .. } => self.check_linear_side(value, false),
            ExprKind::Bv { lhs, rhs, .. } => {
                self.check_linear_side(lhs, false);
                self.check_linear_side(rhs, false);
            }
            _ => {}
        }
    }

    fn nonlinear(&mut self, why: &str, span: Span) {
        if self.opts.allow_nonlinear {
            self.profile.nonlinear_opt_in = true;
            self.warn(
                W_NONLINEAR_OPT_IN,
                format!(
                    "{why}；因启用 `--allow-nonlinear` 而放行，目标将强制为 \
                     `UnknownReviewRequired`（TH-3a，OQ-5 建议删除该开关）"
                ),
                span,
            );
        } else {
            self.err(
                E_NONLINEAR,
                format!("{why}；非线性算术超出可判定片段（G-4），编译期拦截"),
                span,
            );
        }
    }
}

fn describe(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Var(n) => n.clone(),
        ExprKind::FieldAccess { instance, field } => format!("{instance}.{field}"),
        ExprKind::IntLit(v) => v.to_string(),
        ExprKind::RealLit(r) => r.to_string(),
        ExprKind::Arith { op, .. } => op.symbol().to_string(),
        _ => "<表达式>".to_string(),
    }
}

/// 声明级类型与范围检查（实体字段、全局变量、域规模、`@key`）。
pub fn check_declarations(spec: &Spec, tab: &SymbolTable, diags: &mut Vec<Diagnostic>) {
    for e in &spec.entities {
        let mut keys: Vec<&str> = Vec::new();
        let mut field_names: BTreeSet<&str> = BTreeSet::new();
        for f in &e.fields {
            if !field_names.insert(f.name.as_str()) {
                diags.push(
                    Diagnostic::error(
                        E_DUP_NAME,
                        format!("实体 `{}` 的字段 `{}` 重复声明（W1）", e.name, f.name),
                    )
                    .with_span(f.span),
                );
            }
            if f.is_key {
                keys.push(f.name.as_str());
                if !f.sort.is_key_eligible() {
                    diags.push(
                        Diagnostic::error(
                            E_KEY_BAD_SORT,
                            format!(
                                "`@key` 字段 `{}` 的排序为 `{}`，不可作业务主键（07 §7.2.1 禁止 Real/Bool）",
                                f.name,
                                f.sort.source_name()
                            ),
                        )
                        .with_span(f.span),
                    );
                }
            }
            if let Sort::Enum(members) = &f.sort {
                let mut seen = BTreeSet::new();
                for m in members {
                    if !seen.insert(m.as_str()) {
                        diags.push(
                            Diagnostic::error(
                                E_DUP_NAME,
                                format!("`Enum` 成员 `{m}` 重复（字段 `{}`)", f.name),
                            )
                            .with_span(f.span),
                        );
                    }
                }
            }
            check_range(&f.range, &f.sort, f.span, diags);
        }
        if keys.len() > 1 {
            diags.push(
                Diagnostic::error(
                    E_DUP_KEY,
                    format!(
                        "实体 `{}` 有多个 `@key` 字段（{}）；每实体至多一个（07 §7.2.1）",
                        e.name,
                        keys.join(", ")
                    ),
                )
                .with_span(e.span),
            );
        }
    }

    for v in &spec.vars {
        check_range(&v.range, &v.sort, v.span, diags);
    }

    for d in &spec.domains {
        if d.size == 0 {
            diags.push(
                Diagnostic::error(
                    E_RANGE_EMPTY,
                    format!("域 `{}` 的 size 为 0：空域使量词退化且无有效状态（W4）", d.name),
                )
                .with_span(d.span),
            );
        }
    }

    let _ = tab;
}

fn check_range(
    r: &Option<RangeConstraint>,
    sort: &Sort,
    span: Span,
    diags: &mut Vec<Diagnostic>,
) {
    match r {
        None => {}
        Some(RangeConstraint::Length { lo, hi }) => {
            if !matches!(sort, Sort::Str) {
                diags.push(
                    Diagnostic::error(
                        E_SORT_MISMATCH,
                        format!(
                            "`[length: …]` 仅适用于 `String`，实际排序为 `{}`（W2）",
                            sort.source_name()
                        ),
                    )
                    .with_span(span),
                );
            }
            if lo > hi {
                diags.push(
                    Diagnostic::error(
                        E_RANGE_EMPTY,
                        format!("`[length: {lo}..{hi}]` 区间为空（W3）"),
                    )
                    .with_span(span),
                );
            }
        }
        Some(RangeConstraint::Numeric { min, max }) => {
            if !sort.is_numeric() {
                diags.push(
                    Diagnostic::error(
                        E_SORT_MISMATCH,
                        format!(
                            "`[min: …, max: …]` 仅适用于 `Int`/`Real`，实际排序为 `{}`（W2）",
                            sort.source_name()
                        ),
                    )
                    .with_span(span),
                );
            }
            if !matches!(sort, Sort::Int) && !matches!(sort, Sort::Real) {
                // 已在上一分支报错，避免重复
            } else if min.to_f64() > max.to_f64() {
                diags.push(
                    Diagnostic::error(
                        E_RANGE_EMPTY,
                        format!("`[min: {min}, max: {max}]` 区间为空（min > max，W3）"),
                    )
                    .with_span(span),
                );
            }
            if matches!(sort, Sort::Int) {
                if !min.is_integer() || !max.is_integer() {
                    diags.push(
                        Diagnostic::error(
                            E_SORT_MISMATCH,
                            "`Int` 的界值必须为整数",
                        )
                        .with_span(span),
                    );
                }
            }
        }
    }
}


// ═════════════════════════════════════════════════════════════════════════════
// 共享排序规则（单一实现，供本人与 codegen 复用）
// ═════════════════════════════════════════════════════════════════════════════

/// 算术运算符的**唯一**排序规则（`03 §3.4.2`、`N-4`）。
///
/// 特别地，`/` 在两 `Int` 上按**有理除法**解释，其结果排序仍为 `Int`：
/// 由 `TH-4` 交叉相乘在整数内线性化，从而**不离开** `QF_LIA`（`03 §3.11.3`）。
pub fn arith_rule(op: ArithOp, ls: &Sort, rs: &Sort) -> Option<Sort> {
    match op {
        ArithOp::Add | ArithOp::Sub | ArithOp::Mul => {
            if ls.is_numeric() && ls == rs {
                Some(ls.clone())
            } else {
                None
            }
        }
        ArithOp::RealDiv => match (ls, rs) {
            (Sort::Int, Sort::Int) => Some(Sort::Int),
            (Sort::Real, Sort::Real) => Some(Sort::Real),
            _ => None,
        },
        ArithOp::IntDiv | ArithOp::IntMod => {
            if *ls == Sort::Int && *rs == Sort::Int {
                Some(Sort::Int)
            } else {
                None
            }
        }
    }
}

/// **无作用域**的排序推断：用于**已展开**公式（`ALG-1` 之后所有 `FieldAccess` 已成
/// `Flat{domain, index, field}`，量化变量不再存在）。
///
/// 由 `codegen` 用于发射阶段的类型相关决策（`to_real` 包装、枚举成员映射、BV 字面量宽度）。
/// 与 `FormulaChecker` 共用 [`arith_rule`]，保证算术规则单点定义。
pub struct GroundSortCtx<'a> {
    tab: &'a SymbolTable,
    enum_sorts: Vec<Sort>,
}

impl<'a> GroundSortCtx<'a> {
    pub fn new(tab: &'a SymbolTable, spec: &Spec) -> Self {
        let mut enum_sorts: Vec<Sort> = Vec::new();
        for e in &spec.entities {
            for f in &e.fields {
                if matches!(f.sort, Sort::Enum(_)) {
                    enum_sorts.push(f.sort.clone());
                }
            }
        }
        for v in &spec.vars {
            if matches!(v.sort, Sort::Enum(_)) {
                enum_sorts.push(v.sort.clone());
            }
        }
        GroundSortCtx { tab, enum_sorts }
    }

    /// 枚举成员的映射值（成员名 → `0 … k−1`），`DD-6.2`。
    pub fn enum_member_value(&self, name: &str) -> Option<i128> {
        for s in &self.enum_sorts {
            if let Sort::Enum(ms) = s {
                if let Some(i) = ms.iter().position(|m| m == name) {
                    return Some(i as i128);
                }
            }
        }
        None
    }

    /// 某排序的基数（枚举）。`None` 表示该排序不是有限枚举。
    pub fn enum_cardinality(&self, s: &Sort) -> Option<usize> {
        match s {
            Sort::Enum(ms) => Some(ms.len()),
            _ => None,
        }
    }

    pub fn sort_of(&self, e: &Expr) -> Option<Sort> {
        match &e.kind {
            ExprKind::IntLit(_) => Some(Sort::Int),
            ExprKind::RealLit(_) => Some(Sort::Real),
            ExprKind::BoolLit(_) => Some(Sort::Bool),
            ExprKind::StrLit(_) => Some(Sort::Str),
            ExprKind::Var(name) => {
                if let Some(v) = self.tab.vars.get(name) {
                    return Some(v.sort.clone());
                }
                let mut hits: Vec<Sort> = self
                    .enum_sorts
                    .iter()
                    .filter(|s| matches!(s, Sort::Enum(ms) if ms.iter().any(|m| m == name)))
                    .cloned()
                    .collect();
                hits.dedup();
                if hits.len() == 1 {
                    hits.pop()
                } else {
                    None
                }
            }
            ExprKind::Flat { domain, field, .. } => {
                let ent = self.tab.entity_of_domain(domain)?;
                ent.fields
                    .iter()
                    .find(|f| f.name == *field)
                    .map(|f| f.sort.clone())
            }
            ExprKind::FieldAccess { .. } => None, // 展开后不应出现
            ExprKind::Arith { op, lhs, rhs } => {
                let l = self.sort_of(lhs)?;
                let r = self.sort_of(rhs)?;
                let (l, r) = promote_literal(lhs, l, rhs, r);
                arith_rule(*op, &l, &r)
            }
            ExprKind::Neg(a) => self.sort_of(a),
            ExprKind::StrLen(_) => Some(Sort::Int),
            ExprKind::ToReal(_) => Some(Sort::Real),
            ExprKind::Int2Bv { width, .. } => Some(Sort::Bv(*width)),
            ExprKind::Bv2Int(_) => Some(Sort::Int),
            ExprKind::Bv { lhs, .. } => self.sort_of(lhs),
        }
    }
}

/// 比较两操作数排序：仅允许 **`Int` 字面量**在 `Real` 语境下按 `Real` 处理（发射补 `to_real`）。
pub fn promote_literal(le: &Expr, ls: Sort, re: &Expr, rs: Sort) -> (Sort, Sort) {
    let lit = |e: &Expr| matches!(e.kind, ExprKind::IntLit(_) | ExprKind::RealLit(_));
    match (&ls, &rs) {
        (Sort::Int, Sort::Real) if lit(le) => (Sort::Real, rs),
        (Sort::Real, Sort::Int) if lit(re) => (ls, Sort::Real),
        _ => (ls, rs),
    }
}
