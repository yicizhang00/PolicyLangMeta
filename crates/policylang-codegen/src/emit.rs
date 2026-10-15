//! SMT-LIB2 脚本生成与六式目标编码（`06 §6.1`–`§6.3`）。
//!
//! - 骨架与命令序约束：`CO-1`…`CO-6`（§6.1.1/§6.1.2）
//! - 声明发射顺序 `DET`（§6.2.2）：全局变量按声明序 → 域按声明序 → 索引升序 → 字段声明序
//! - 边界断言 `Bnd`（§6.2.4）：**不带 `:named`**（`DD-3.1`），避免污染 Unsat Core
//! - 六式目标：`consistency` / `invariant` / `refines`（双查询）/ `completeness` / `safety` / `mutex`（§6.3）
//!
//! **一目标一查询文件**（`CO-4` / `DD-6.1`）：不使用 `(push)/(pop)`，故与首胜强杀不冲突。

use policylang_ast::formula::{
    ArithOp, Atom, CmpOp, Expr, ExprKind, Formula, FormulaKind, Rational, RegLan, Sort,
};
use policylang_ast::naming;
use policylang_ast::spec::{RangeConstraint, Spec, TargetType};
use policylang_ast::Span;
use policylang_check::typecheck::{promote_literal, GroundSortCtx};
use policylang_check::SymbolTable;

use crate::smt_value as v;

/// 期望的求解器回答（决定 PASS/FAIL）。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpectedVerdict {
    /// `sat` 即通过（`consistency`）。
    Sat,
    /// `unsat` 即通过（其余五式）。
    Unsat,
}

/// 一条可独立求解的查询（一目标一文件，`CO-4`）。
#[derive(Debug, Clone)]
pub struct EmittedQuery {
    pub goal_name: String,
    pub target_type: TargetType,
    pub logic: String,
    pub script: String,
    pub expected: ExpectedVerdict,
    /// 反证断言标签（唯一一条）：用于**空真检测**（`06 §6.3.7`）。
    /// Core 中若**不含**它，则该 UNSAT 完全由前提贡献 ⇒ 空真告警。
    pub refutation_label: Option<String>,
    /// 脚本中全部 `:named` 标签（按发射顺序）。
    pub labels: Vec<String>,
    /// 附加说明（如 `safety_vacuous`）。
    pub notes: Vec<String>,
}

impl EmittedQuery {
    /// `query_hash` 的规范输入（`CO-5`：UTF-8 无 BOM、LF、末尾换行）。
    pub fn canonical(&self) -> String {
        let mut s = self.script.clone();
        if !s.ends_with('\n') {
            s.push('\n');
        }
        s.replace("\r\n", "\n")
    }
}

/// 一个已声明符号（含其范围约束），发射顺序即向量顺序（`DET`）。
#[derive(Debug, Clone)]
pub struct SymbolDecl {
    pub symbol: String,
    pub sort: Sort,
    pub range: Option<RangeConstraint>,
}

/// 枚举编码方式（`DD-6.2`）。
///
/// 规范默认 **有界整数编码**（成员按声明序映射到 `0 … k−1`，配成员闭包断言）；
/// `Datatype` 是**保留开关**，仅在 `ALG-3` 确认后端支持相应档位时可启用。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum EnumEncoding {
    /// 有界整数编码 + `(or (= x 0) … (= x k−1))` 闭包断言（默认）。
    #[default]
    Int,
    /// SMT-LIB2 `declare-datatype` 代数数据类型。
    ///
    /// 代价：逻辑档位离开 `QF_*` 标准集（须 `ALL`），见 `DD-6.2` 的取舍说明；
    /// 收益：类型本身即闭集，**无需**成员闭包断言，且模型值直接是构造子名。
    Datatype,
}

/// 发射上下文。
pub struct Emitter<'a> {
    spec: &'a Spec,
    tab: &'a SymbolTable,
    sorts: GroundSortCtx<'a>,
    /// 脚本头部注释（含 `spec_hash` 等审计信息）。
    pub header: String,
    /// 是否发射 `Bnd`。
    pub emit_bounds: bool,
    /// 枚举编码方式（`DD-6.2`）。
    pub enum_encoding: EnumEncoding,
}

impl<'a> Emitter<'a> {
    pub fn new(spec: &'a Spec, tab: &'a SymbolTable, header: String) -> Self {
        Emitter {
            spec,
            tab,
            sorts: GroundSortCtx::new(tab, spec),
            header,
            emit_bounds: true,
            enum_encoding: EnumEncoding::default(),
        }
    }

    /// 设置枚举编码方式（构造期配置，`DD-6.2`）。
    pub fn with_enum_encoding(mut self, e: EnumEncoding) -> Self {
        self.enum_encoding = e;
        self
    }

    /// 需要 `declare-datatype` 的枚举类型，**按类型名排序**（确定性）。
    fn enum_datatypes(&self) -> Vec<(String, Vec<String>)> {
        let mut m: std::collections::BTreeMap<String, Vec<String>> =
            std::collections::BTreeMap::new();
        for d in self.decls() {
            if let Sort::Enum(members) = &d.sort {
                if !members.is_empty() {
                    m.entry(naming::enum_type_name(members))
                        .or_insert_with(|| members.clone());
                }
            }
        }
        m.into_iter().collect()
    }

    pub fn sorts(&self) -> &GroundSortCtx<'a> {
        &self.sorts
    }

    /// `DET`：确定性的符号声明顺序。
    pub fn decls(&self) -> Vec<SymbolDecl> {
        let mut out = Vec::new();
        for var in &self.spec.vars {
            out.push(SymbolDecl {
                symbol: naming::global_symbol(&var.name),
                sort: var.sort.clone(),
                range: var.range.clone(),
            });
        }
        for d in &self.spec.domains {
            let Some(ent) = self.tab.entities.get(&d.entity) else {
                continue;
            };
            for i in 0..d.size {
                for f in &ent.fields {
                    out.push(SymbolDecl {
                        symbol: naming::scalar_symbol(&d.name, i as usize, &f.name),
                        sort: f.sort.clone(),
                        range: f.range.clone(),
                    });
                }
            }
        }
        out
    }

    /// 脚本前导：`CO-1`/`CO-2` 的命令 + 声明 + `Bnd`。
    fn prelude(&self, logic: &str) -> String {
        let mut s = String::new();
        if !self.header.is_empty() {
            for line in self.header.lines() {
                s.push_str("; ");
                s.push_str(line);
                s.push('\n');
            }
        }
        s.push_str("; 本文件由 policylang codegen 生成，用于审计复算；请勿手工修改。\n");
        // CO-1：set-logic 必须为首个命令
        s.push_str(&format!("(set-logic {logic})\n"));
        // CO-2：set-option 先于任何 declare-fun / assert
        s.push_str("(set-option :produce-models true)\n");
        s.push_str("(set-option :produce-unsat-cores true)\n");
        s.push_str("(set-option :print-success false)\n");
        // DD-6.2（datatype 编码）：枚举类型必须先于使用它的常量声明
        if self.enum_encoding == EnumEncoding::Datatype {
            for (tname, members) in self.enum_datatypes() {
                let ctors: Vec<String> = members
                    .iter()
                    .map(|m| format!("({})", naming::enum_ctor_name(m)))
                    .collect();
                s.push_str(&format!("(declare-datatype {tname} ({}))\n", ctors.join(" ")));
            }
        }
        // CO-3：全部 declare-fun 先于首个 assert
        for d in self.decls() {
            s.push_str(&format!(
                "(declare-fun {} () {})\n",
                d.symbol,
                self.sort_name(&d.sort)
            ));
        }
        if self.emit_bounds {
            for d in self.decls() {
                if let Some(b) = self.bound_assert(&d) {
                    s.push_str(&b);
                }
            }
        }
        // CO-5：末尾必须换行（由调用方在 finish 时保证）
        s
    }

    fn sort_name(&self, s: &Sort) -> String {
        match s {
            Sort::Int => "Int".into(),
            Sort::Real => "Real".into(),
            Sort::Bool => "Bool".into(),
            Sort::Str => "String".into(),
            Sort::Bv(w) => v::bv_sort(*w),
            // DD-6.2：Enum 默认**有界整数编码**；datatype 开关下用生成的类型名
            Sort::Enum(members) => match self.enum_encoding {
                EnumEncoding::Int => "Int".into(),
                EnumEncoding::Datatype => naming::enum_type_name(members),
            },
        }
    }

    /// `Bnd`（`06 §6.2.4`）：**不带 `:named`**；`Bool`/`BV` 不发射。
    fn bound_assert(&self, d: &SymbolDecl) -> Option<String> {
        let sym = &d.symbol;
        match (&d.range, &d.sort) {
            (Some(RangeConstraint::Numeric { min, max }), Sort::Int) => Some(format!(
                "(assert (and (<= {} {}) (<= {} {})))\n",
                v::int_lit(min.num / min.den),
                sym,
                sym,
                v::int_lit(max.num / max.den)
            )),
            (Some(RangeConstraint::Numeric { min, max }), Sort::Real) => Some(format!(
                "(assert (and (<= {} {}) (<= {} {})))\n",
                v::real_lit(min),
                sym,
                sym,
                v::real_lit(max)
            )),
            (Some(RangeConstraint::Length { lo, hi }), Sort::Str) => Some(format!(
                "(assert (and (<= {} (str.len {})) (<= (str.len {}) {})))\n",
                v::int_lit(*lo as i128),
                sym,
                sym,
                v::int_lit(*hi as i128)
            )),
            (None, Sort::Enum(_)) if self.enum_encoding == EnumEncoding::Datatype => {
                // datatype 是**闭类型**：任何值都必然是某个构造子 ⇒ 无需成员闭包断言
                None
            }
            (None, Sort::Enum(members)) => {
                // 注意：`join("or", …)` **自带外层括号**（见文件末尾的 `join`），
                // 因此这里**不能**再补一层——否则产出 `(assert ((or …)))`。
                // 实测后果极严重：z3 报 `invalid function application` 并**丢弃该断言**，
                // 但随后仍对剩余断言给出 `unsat` ⇒ 枚举变量退化为无界 `Int`，
                // 可能产生**假证明**（与 `G-4`/`G-8` 直接冲突）。
                if members.is_empty() {
                    // 空枚举没有任何合法取值 ⇒ 该域为空（`E-EMPTY-CARRIER` 的语义兜底）
                    return Some("(assert false)\n".to_string());
                }
                let disj: Vec<String> = (0..members.len())
                    .map(|i| format!("(= {sym} {i})"))
                    .collect();
                Some(format!("(assert {})\n", join("or", &disj)))
            }
            _ => None,
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // 表达式与公式发射
    // ─────────────────────────────────────────────────────────────────────────

    /// 发射表达式；`as_real = true` 时，若该表达式排序为 `Int` 则补 `(to_real …)`。
    pub fn expr(&self, e: &Expr, as_real: bool) -> String {
        match &e.kind {
            ExprKind::IntLit(n) => {
                if as_real {
                    v::to_real(&v::int_lit(*n))
                } else {
                    v::int_lit(*n)
                }
            }
            ExprKind::RealLit(r) => v::real_lit(r),
            ExprKind::BoolLit(b) => v::bool_lit(*b),
            ExprKind::StrLit(s) => v::str_lit(s),
            ExprKind::Var(name) => {
                if let Some(v0) = self.tab.vars.get(name) {
                    let _ = v0;
                    naming::global_symbol(name)
                } else if let Some(idx) = self.sorts.enum_member_value(name) {
                    match self.enum_encoding {
                        // 有界整数编码（DD-6.2 默认）
                        EnumEncoding::Int => {
                            if as_real {
                                v::to_real(&v::int_lit(idx))
                            } else {
                                v::int_lit(idx)
                            }
                        }
                        // datatype 构造子（零元构造子本身即为项）
                        EnumEncoding::Datatype => naming::enum_ctor_name(name),
                    }
                } else {
                    naming::global_symbol(name)
                }
            }
            ExprKind::Flat {
                domain,
                index,
                field,
            } => naming::scalar_symbol(domain, *index, field),
            ExprKind::FieldAccess { instance, field } => {
                // 展开后不应出现；保守降级为可读符号（不静默丢失）
                naming::scalar_symbol(instance, 0, field)
            }
            ExprKind::Arith { op, lhs, rhs } => {
                let rs = self.sorts.sort_of(e);
                let l = self.operand(lhs, rhs);
                let r = self.operand(rhs, lhs);
                let sym = match op {
                    ArithOp::Add => "+",
                    ArithOp::Sub => "-",
                    ArithOp::Mul => "*",
                    // 线性化后不应残留 `/`；若残留则按排序选择（Int 用 div 以免非法项）
                    ArithOp::RealDiv => match rs {
                        Some(Sort::Int) => "div",
                        _ => "/",
                    },
                    ArithOp::IntDiv => "div",
                    ArithOp::IntMod => "mod",
                };
                format!("({sym} {l} {r})")
            }
            ExprKind::Neg(a) => format!("(- {})", self.expr(a, false)),
            ExprKind::StrLen(a) => format!("(str.len {})", self.expr(a, false)),
            ExprKind::ToReal(a) => v::to_real(&self.expr(a, false)),
            ExprKind::Int2Bv { width, value } => {
                format!("((_ int_to_bv {width}) {})", self.expr(value, false))
            }
            ExprKind::Bv2Int(a) => format!("(bv2int {})", self.expr(a, false)),
            ExprKind::Bv {
                op,
                lhs,
                rhs,
                width,
            } => {
                let _ = width;
                if op.is_unary() {
                    format!("({} {})", op.smt_name(), self.expr(lhs, false))
                } else {
                    format!(
                        "({} {} {})",
                        op.smt_name(),
                        self.expr(lhs, false),
                        self.expr(rhs, false)
                    )
                }
            }
        }
    }

    /// 二元运算的操作数：仅在**排序需要**时给 `Int` 侧补 `to_real`（`N-4` 的字面量提升）。
    fn operand(&self, e: &Expr, other: &Expr) -> String {
        let se = self.sorts.sort_of(e);
        let so = self.sorts.sort_of(other);
        let (a, _) = match (se, so) {
            (Some(a), Some(b)) => {
                let (x, y) = promote_literal(e, a, other, b);
                (x, y)
            }
            _ => return self.expr(e, false),
        };
        self.expr(e, a == Sort::Real && !matches!(e.kind, ExprKind::RealLit(_)))
    }

    /// 发射公式。
    pub fn formula(&self, f: &Formula) -> String {
        match &f.kind {
            FormulaKind::True => "true".into(),
            FormulaKind::False => "false".into(),
            FormulaKind::Atom(a) => self.atom(a),
            FormulaKind::Not(x) => format!("(not {})", self.formula(x)),
            FormulaKind::And(vs) => {
                if vs.is_empty() {
                    "true".into()
                } else {
                    format!(
                        "{}",
                        join("and", &vs.iter().map(|x| self.formula(x)).collect::<Vec<_>>())
                    )
                }
            }
            FormulaKind::Or(vs) => {
                if vs.is_empty() {
                    "false".into()
                } else {
                    format!(
                        "{}",
                        join("or", &vs.iter().map(|x| self.formula(x)).collect::<Vec<_>>())
                    )
                }
            }
            FormulaKind::Implies(a, b) => {
                format!("(=> {} {})", self.formula(a), self.formula(b))
            }
            FormulaKind::Iff(a, b) => format!("(= {} {})", self.formula(a), self.formula(b)),
            FormulaKind::Forall { .. } | FormulaKind::Exists { .. } => {
                // INV-G 违反：展开器保证不出现。此处保守报错文本（不可解析），使问题显性化。
                "(error \"INV-G violated: quantifier survived grounding\")".into()
            }
            FormulaKind::MatchesAll { subject, patterns } => {
                if patterns.is_empty() {
                    return "true".into();
                }
                let regs: Vec<String> = patterns
                    .iter()
                    .map(|p| match policylang_check::guardian::parse_r_sub(p, f.span) {
                        Ok(r) => r.to_smt(),
                        Err(_) => RegLan::Empty.to_smt(),
                    })
                    .collect();
                let re = if regs.len() == 1 {
                    regs[0].clone()
                } else {
                    join("re.inter", &regs)
                };
                format!("(str.in_re {} {re})", self.expr(subject, false))
            }
            FormulaKind::InCidr { subject, cidr } => {
                // TH-5：`(= (bvand e mask) net0)`
                let mask = cidr.mask();
                format!(
                    "(= (bvand {} {}) {})",
                    self.expr(subject, false),
                    v::bv_lit(mask, cidr.width),
                    v::bv_lit(cidr.net0 & mask, cidr.width)
                )
            }
            FormulaKind::InRange {
                subject,
                width,
                lo_val,
                hi_val,
                ..
            } => format!(
                "(and (bvule {} {}) (bvule {} {}))",
                v::bv_lit(*lo_val, *width),
                self.expr(subject, false),
                self.expr(subject, false),
                v::bv_lit(*hi_val, *width)
            ),
            FormulaKind::Unique { .. } => {
                "(error \"Unique must be grounded before emission\")".into()
            }
        }
    }

    fn atom(&self, a: &Atom) -> String {
        match a {
            Atom::Bool(e) => self.expr(e, false),
            Atom::Cmp { lhs, op, rhs } => {
                let l = self.operand(lhs, rhs);
                let r = self.operand(rhs, lhs);
                match op {
                    CmpOp::Eq => format!("(= {l} {r})"),
                    CmpOp::Ne => format!("(distinct {l} {r})"),
                    CmpOp::Lt => format!("(< {l} {r})"),
                    CmpOp::Le => format!("(<= {l} {r})"),
                    // SMT-LIB 无 `>`/`>=`：交换两侧
                    CmpOp::Gt => format!("(< {r} {l})"),
                    CmpOp::Ge => format!("(<= {r} {l})"),
                    CmpOp::StrLt => format!("(str.< {l} {r})"),
                    CmpOp::StrLe => format!("(str.<= {l} {r})"),
                }
            }
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // 六式目标编码（06 §6.3）
    // ─────────────────────────────────────────────────────────────────────────

    /// `consistency(P)`：`sat` 即 PASS；`unsat` ⇒ FAIL（取 Unsat Core 归因规则）。
    pub fn consistency(
        &self,
        policy: &str,
        rules: &[(String, Formula)],
        logic: &str,
    ) -> EmittedQuery {
        let mut s = self.prelude(logic);
        let mut labels = Vec::new();
        for (rule, f) in rules {
            let label = naming::label_rule(policy, rule);
            s.push_str(&format!(
                "(assert (! {} :named {}))\n",
                self.formula(f),
                label
            ));
            labels.push(label);
        }
        s.push_str("(check-sat)\n(get-model)\n(get-unsat-core)\n");
        EmittedQuery {
            goal_name: format!("{policy}::consistency::Consistency"),
            target_type: TargetType::Consistency,
            logic: logic.to_string(),
            script: s,
            expected: ExpectedVerdict::Sat,
            refutation_label: None,
            labels,
            notes: Vec::new(),
        }
    }

    /// `invariant(Inv, P)`：`unsat` 即 PASS；只有 `¬Inv` 带标签以便区分「空真 PASS」。
    pub fn invariant(
        &self,
        policy: &str,
        inv_name: &str,
        rules: &[(String, Formula)],
        inv: &Formula,
        logic: &str,
    ) -> EmittedQuery {
        let mut s = self.prelude(logic);
        for (_, f) in rules {
            s.push_str(&format!("(assert {})\n", self.formula(f)));
        }
        let label = naming::label_invariant(inv_name);
        s.push_str(&format!(
            "(assert (! (not {}) :named {}))\n",
            self.formula(inv),
            label
        ));
        s.push_str("(check-sat)\n(get-model)\n(get-unsat-core)\n");
        EmittedQuery {
            goal_name: format!("{policy}::invariant::{inv_name}"),
            target_type: TargetType::Invariant,
            logic: logic.to_string(),
            script: s,
            expected: ExpectedVerdict::Unsat,
            refutation_label: Some(label.clone()),
            labels: vec![label],
            notes: Vec::new(),
        }
    }

    /// `completeness(P)`（模式 A：全域完备）：`¬⋁branches` SAT ⇒ 死区反例。
    pub fn completeness(
        &self,
        policy: &str,
        premises: &[(String, Formula)],
        branches: &[(String, Formula)],
        logic: &str,
    ) -> EmittedQuery {
        let mut s = self.prelude(logic);
        for (_, f) in premises {
            s.push_str(&format!("(assert {})\n", self.formula(f)));
        }
        let label = naming::label_completeness(policy);
        let disj: Vec<String> = branches.iter().map(|(_, f)| self.formula(f)).collect();
        let body = if disj.is_empty() {
            "false".to_string()
        } else {
            join("or", &disj)
        };
        s.push_str(&format!(
            "(assert (! (not {body}) :named {}))\n",
            label
        ));
        s.push_str("(check-sat)\n(get-model)\n(get-unsat-core)\n");
        EmittedQuery {
            goal_name: format!("{policy}::completeness::Coverage"),
            target_type: TargetType::Completeness,
            logic: logic.to_string(),
            script: s,
            expected: ExpectedVerdict::Unsat,
            refutation_label: Some(label.clone()),
            labels: vec![label],
            notes: Vec::new(),
        }
    }

    /// `safety(P)`：**查询不含除法**（分母表达式已在 `ALG-2` 中取出）。
    pub fn safety(
        &self,
        policy: &str,
        rules: &[(String, Formula)],
        divisors: &[Expr],
        logic: &str,
    ) -> EmittedQuery {
        let mut s = self.prelude(logic);
        for (_, f) in rules {
            s.push_str(&format!("(assert {})\n", self.formula(f)));
        }
        let label = naming::label_safety_divzero(policy);
        let mut notes = Vec::new();
        if divisors.is_empty() {
            // `k = 0` ⇒ Pass，但**必须**诚实标注 `safety_vacuous`（06 §6.3.5）
            notes.push("safety_vacuous: true".to_string());
        }
        let disj: Vec<String> = divisors
            .iter()
            .map(|d| {
                let sd = self.sorts.sort_of(d);
                let zero = if sd == Some(Sort::Real) {
                    "0.0".to_string()
                } else {
                    "0".to_string()
                };
                format!("(= {} {zero})", self.expr(d, false))
            })
            .collect();
        let body = if disj.is_empty() {
            "false".to_string()
        } else {
            join("or", &disj)
        };
        s.push_str(&format!("(assert (! {body} :named {}))\n", label));
        s.push_str("(check-sat)\n(get-model)\n(get-unsat-core)\n");
        EmittedQuery {
            goal_name: format!("{policy}::safety::DivisionTotal"),
            target_type: TargetType::Safety,
            logic: logic.to_string(),
            script: s,
            expected: ExpectedVerdict::Unsat,
            refutation_label: Some(label.clone()),
            labels: vec![label],
            notes,
        }
    }

    /// `mutex(P)` 的第 `(i, j)` 对：一个独立查询文件（`CO-4`）。
    pub fn mutex_pair(
        &self,
        policy: &str,
        i: usize,
        j: usize,
        bi: &Formula,
        bj: &Formula,
        logic: &str,
    ) -> EmittedQuery {
        let mut s = self.prelude(logic);
        let label = naming::label_mutex(policy, i, j);
        s.push_str(&format!(
            "(assert (! (and {} {}) :named {}))\n",
            self.formula(bi),
            self.formula(bj),
            label
        ));
        s.push_str("(check-sat)\n(get-model)\n(get-unsat-core)\n");
        EmittedQuery {
            goal_name: format!("{policy}::mutex::{i}_{j}"),
            target_type: TargetType::Mutex,
            logic: logic.to_string(),
            script: s,
            expected: ExpectedVerdict::Unsat,
            refutation_label: Some(label.clone()),
            labels: vec![label],
            notes: Vec::new(),
        }
    }

    /// `refines` 的 `Q1`：`R_new ∧ ¬R_old`（SAT ⇒ 新策略放宽了暴露面）。
    pub fn refines_q1(
        &self,
        new_policy: &str,
        old_policy: &str,
        new_rules: &[(String, Formula)],
        old_rules: &[(String, Formula)],
        logic: &str,
    ) -> EmittedQuery {
        self.refines_one(new_policy, old_policy, new_rules, old_rules, logic, true)
    }

    /// `refines` 的 `Q2`：`R_old ∧ ¬R_new`。
    pub fn refines_q2(
        &self,
        new_policy: &str,
        old_policy: &str,
        new_rules: &[(String, Formula)],
        old_rules: &[(String, Formula)],
        logic: &str,
    ) -> EmittedQuery {
        self.refines_one(new_policy, old_policy, new_rules, old_rules, logic, false)
    }

    #[allow(clippy::too_many_arguments)]
    fn refines_one(
        &self,
        new_policy: &str,
        old_policy: &str,
        new_rules: &[(String, Formula)],
        old_rules: &[(String, Formula)],
        logic: &str,
        q1: bool,
    ) -> EmittedQuery {
        let (head_policy, head_rules, tail_policy, tail_rules) = if q1 {
            (new_policy, new_rules, old_policy, old_rules)
        } else {
            (old_policy, old_rules, new_policy, new_rules)
        };
        let mut s = self.prelude(logic);
        let mut labels = Vec::new();
        for (rule, f) in head_rules {
            let label = naming::label_rule(head_policy, rule);
            s.push_str(&format!(
                "(assert (! {} :named {}))\n",
                self.formula(f),
                label
            ));
            labels.push(label);
        }
        let neg_label = naming::label_old_neg(tail_policy);
        let conj: Vec<String> = tail_rules.iter().map(|(_, f)| self.formula(f)).collect();
        let body = if conj.is_empty() {
            "true".to_string()
        } else {
            join("and", &conj)
        };
        s.push_str(&format!(
            "(assert (! (not {body}) :named {}))\n",
            neg_label
        ));
        labels.push(neg_label.clone());
        s.push_str("(check-sat)\n(get-model)\n(get-unsat-core)\n");
        EmittedQuery {
            goal_name: format!(
                "{new_policy}::refines::{old_policy}::{}",
                if q1 { "Q1" } else { "Q2" }
            ),
            target_type: TargetType::Refines,
            logic: logic.to_string(),
            script: s,
            expected: ExpectedVerdict::Unsat,
            refutation_label: Some(neg_label),
            labels,
            notes: vec![if q1 {
                "Q1: R_new ∧ ¬R_old（SAT ⇒ 放宽）".to_string()
            } else {
                "Q2: R_old ∧ ¬R_new（SAT ⇒ 可比较性判别）".to_string()
            }],
        }
    }

    /// 未通过检查时用于构造 `Error` 级查询（不求解，直接给出退出码 3/4 的依据）。
    pub fn error_query(goal_name: &str, target_type: TargetType, note: &str) -> EmittedQuery {
        EmittedQuery {
            goal_name: goal_name.to_string(),
            target_type,
            logic: "".into(),
            script: String::new(),
            expected: ExpectedVerdict::Unsat,
            refutation_label: None,
            labels: Vec::new(),
            notes: vec![format!("compile_error: {note}")],
        }
    }
}

fn join(op: &str, items: &[String]) -> String {
    match items.len() {
        0 => format!("({op})"),
        1 => items[0].clone(),
        _ => format!("({op} {})", items.join(" ")),
    }
}

/// 排序辅助（供外部构造 `Span`）。
pub fn dummy_span() -> Span {
    Span::default()
}

/// `Rational` 的便利构造（供测试与外部）。
pub fn rat(n: i128, d: i128) -> Option<Rational> {
    Rational::new(n, d)
}
