//! 排序系统、精确有理数与表达式/公式的抽象语法（`05 §3`、`03 §3.2`）。
//!
//! 与 Lean 侧 `PolicylangProof/Syntax.lean` 的对应关系见 `12 §12.5.1`（AST 一致性契约）。

use serde::{Deserialize, Serialize};
use std::fmt;

use crate::span::Span;

// ─────────────────────────────────────────────────────────────────────────────
// 排序
// ─────────────────────────────────────────────────────────────────────────────

/// 排序（`03 §3.2.1`）。`IPv4`/`IPv6` 是 `Bv(32)`/`Bv(128)` 的**语法别名**（`04 §4`）。
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Sort {
    Int,
    Real,
    Bool,
    Str,
    /// 位向量宽度（IPv4 = 32，IPv6 = 128）。
    Bv(u32),
    /// 枚举：成员名按**声明序**映射到 `0 … k−1`（`DD-6.2` 有界整数编码）。
    Enum(Vec<String>),
}

impl Sort {
    /// 报告/诊断中使用的排序名（与 `report.schema.json` 的 `Sort` 枚举一致）。
    pub fn display_name(&self) -> &'static str {
        match self {
            Sort::Int => "Int",
            Sort::Real => "Real",
            Sort::Bool => "Bool",
            Sort::Str => "Str",
            Sort::Bv(32) => "IPv4",
            Sort::Bv(128) => "IPv6",
            Sort::Bv(_) => "BitVec",
            Sort::Enum(_) => "Enum",
        }
    }

    /// 源语言书写形（`Int` / `IPv4` / `BitVec(16)` / `Enum { A, B }`）。
    pub fn source_name(&self) -> String {
        match self {
            Sort::Int => "Int".into(),
            Sort::Real => "Real".into(),
            Sort::Bool => "Bool".into(),
            Sort::Str => "String".into(),
            Sort::Bv(32) => "IPv4".into(),
            Sort::Bv(128) => "IPv6".into(),
            Sort::Bv(n) => format!("BitVec({n})"),
            Sort::Enum(members) => format!("Enum {{ {} }}", members.join(", ")),
        }
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self, Sort::Int | Sort::Real)
    }

    pub fn is_bitvec(&self) -> bool {
        matches!(self, Sort::Bv(_))
    }

    /// 是否可作业务主键（`@key`）：`Real`（不稳定）与 `Bool`（区分度不足）被禁止（`07 §7.2.1`）。
    pub fn is_key_eligible(&self) -> bool {
        match self {
            Sort::Real | Sort::Bool => false,
            Sort::Int | Sort::Str | Sort::Bv(_) | Sort::Enum(_) => true,
        }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.source_name())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 精确有理数
// ─────────────────────────────────────────────────────────────────────────────

/// 精确有理数（取代上游 `f64`，修正 `C-6`；与 `03 §3.2.3 N-1` 一致）。
///
/// 不变式：`den > 0` 且 `gcd(|num|, den) == 1`；`den == 0` 非法。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Rational {
    pub num: i128,
    pub den: i128,
}

fn gcd(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

impl Rational {
    /// 构造并规范化。`den == 0` 时返回 `None`（由调用方转为诊断，绝不 panic）。
    pub fn new(num: i128, den: i128) -> Option<Self> {
        if den == 0 {
            return None;
        }
        let (mut n, mut d) = (num, den);
        if d < 0 {
            n = -n;
            d = -d;
        }
        let g = gcd(n, d);
        if g > 1 {
            n /= g;
            d /= g;
        }
        Some(Rational { num: n, den: d })
    }

    pub const fn from_int(v: i128) -> Self {
        Rational { num: v, den: 1 }
    }

    pub fn is_integer(&self) -> bool {
        self.den == 1
    }

    pub fn is_zero(&self) -> bool {
        self.num == 0
    }

    pub fn is_negative(&self) -> bool {
        self.num < 0
    }

    pub fn to_f64(&self) -> f64 {
        self.num as f64 / self.den as f64
    }

    /// 上取整（用于 `str.len` 等整型位置的字面量校验）。
    pub fn ceil_i128(&self) -> i128 {
        let q = self.num.div_euclid(self.den);
        if self.num.rem_euclid(self.den) == 0 {
            q
        } else {
            q + 1
        }
    }

    /// 十进制整数字面量（`number` 解析结果）→ 有理数。
    pub fn parse_decimal(text: &str) -> Option<Self> {
        let t = text.trim();
        let neg = t.starts_with('-');
        let body = t.trim_start_matches(['+', '-']);
        let mut parts = body.splitn(2, '.');
        let int_part = parts.next()?;
        let frac_part = parts.next().unwrap_or("");
        let mut num: i128 = int_part.parse().ok()?;
        let mut den: i128 = 1;
        for ch in frac_part.chars() {
            let d = ch.to_digit(10)? as i128;
            num = num.checked_mul(10)?.checked_add(d)?;
            den = den.checked_mul(10)?;
        }
        if neg {
            num = -num;
        }
        Rational::new(num, den)
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den == 1 {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 表达式
// ─────────────────────────────────────────────────────────────────────────────

/// 算术运算符（`04 §5`）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    /// `/`（Real 除法；可变分母由 `TH-4` 线性化）
    RealDiv,
    /// `div`（整数除法，常量除数）
    IntDiv,
    /// `mod`（整数取模，常量除数）
    IntMod,
}

impl ArithOp {
    pub fn symbol(self) -> &'static str {
        match self {
            ArithOp::Add => "+",
            ArithOp::Sub => "-",
            ArithOp::Mul => "*",
            ArithOp::RealDiv => "/",
            ArithOp::IntDiv => "div",
            ArithOp::IntMod => "mod",
        }
    }

    pub fn is_div_like(self) -> bool {
        matches!(self, ArithOp::RealDiv | ArithOp::IntDiv | ArithOp::IntMod)
    }
}

/// 位向量运算（`04 §5`）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BvOp {
    And,
    Or,
    Xor,
    Not,
    Add,
    Sub,
    Mul,
    Shl,
    Lshr,
}

impl BvOp {
    pub fn smt_name(self) -> &'static str {
        match self {
            BvOp::And => "bvand",
            BvOp::Or => "bvor",
            BvOp::Xor => "bvxor",
            BvOp::Not => "bvnot",
            BvOp::Add => "bvadd",
            BvOp::Sub => "bvsub",
            BvOp::Mul => "bvmul",
            BvOp::Shl => "bvshl",
            BvOp::Lshr => "bvlshr",
        }
    }

    pub fn is_unary(self) -> bool {
        matches!(self, BvOp::Not)
    }
}

/// 表达式的语法节点。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExprKind {
    IntLit(i128),
    RealLit(Rational),
    BoolLit(bool),
    StrLit(String),
    /// 全局变量（`GVar`）。
    Var(String),
    /// 绑定变量字段访问 `s.port`。
    FieldAccess { instance: String, field: String },
    /// 展平后的域实例标量 `PL_<D>_<i>_<f>`（`ground` 的产物，`A-7`）。
    Flat {
        domain: String,
        index: usize,
        field: String,
    },
    Arith {
        op: ArithOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Neg(Box<Expr>),
    /// `str.len(e)`
    StrLen(Box<Expr>),
    /// `to_real(e)`（显式 Int→Real 提升，`N-4`）
    ToReal(Box<Expr>),
    /// `int2bv(n, e)`
    Int2Bv { width: u32, value: Box<Expr> },
    /// `bv2int(e)`（编译期拒绝，保留以求诊断友好）
    Bv2Int(Box<Expr>),
    Bv {
        op: BvOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        width: u32,
    },
}

/// 带跨度的表达式。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Expr { kind, span }
    }

    pub fn int(v: i128, span: Span) -> Self {
        Expr::new(ExprKind::IntLit(v), span)
    }

    pub fn var(name: &str, span: Span) -> Self {
        Expr::new(ExprKind::Var(name.to_string()), span)
    }

    /// 常量折叠所需的静态判定：是否为数值字面量。
    pub fn as_int_lit(&self) -> Option<i128> {
        match &self.kind {
            ExprKind::IntLit(v) => Some(*v),
            _ => None,
        }
    }

    pub fn as_num_lit(&self) -> Option<Rational> {
        match &self.kind {
            ExprKind::IntLit(v) => Some(Rational::from_int(*v)),
            ExprKind::RealLit(r) => Some(*r),
            _ => None,
        }
    }

    /// 是否为**字面量常量**（`E-` 层判定用，`03 §3.4.1` 的 `isConst`）。
    pub fn is_constant(&self) -> bool {
        match &self.kind {
            ExprKind::IntLit(_) | ExprKind::RealLit(_) | ExprKind::BoolLit(_) | ExprKind::StrLit(_) => true,
            ExprKind::Neg(e) => e.is_constant(),
            ExprKind::ToReal(e) => e.is_constant(),
            ExprKind::Arith { lhs, rhs, .. } => lhs.is_constant() && rhs.is_constant(),
            _ => false,
        }
    }

    /// 是否**必然为整数**（`div`/`mod`/`str.len` 结果为 `Int`）。
    pub fn is_int_shaped(&self) -> bool {
        match &self.kind {
            ExprKind::IntLit(_) | ExprKind::StrLen(_) | ExprKind::Bv2Int(_) => true,
            ExprKind::Arith { op, .. } => {
                matches!(op, ArithOp::IntDiv | ArithOp::IntMod)
            }
            _ => false,
        }
    }

    /// `name` 是否作为**域实例**出现在本表达式中（`FieldAccess.instance == name`）。
    ///
    /// 用于 `ALG-1` 的死变量剪枝与 `W11` 的精确度量：未被使用的量化变量不参与枚举。
    pub fn occurs_instance(&self, name: &str) -> bool {
        match &self.kind {
            ExprKind::FieldAccess { instance, .. } => instance == name,
            ExprKind::Arith { lhs, rhs, .. } => {
                lhs.occurs_instance(name) || rhs.occurs_instance(name)
            }
            ExprKind::Bv { lhs, rhs, .. } => lhs.occurs_instance(name) || rhs.occurs_instance(name),
            ExprKind::Neg(a)
            | ExprKind::StrLen(a)
            | ExprKind::ToReal(a)
            | ExprKind::Bv2Int(a) => a.occurs_instance(name),
            ExprKind::Int2Bv { value, .. } => value.occurs_instance(name),
            _ => false,
        }
    }

    /// 是否为**非常量除数的除法**（`/`），或 `div`/`mod` 的非常量除数。
    pub fn has_nonconst_divisor(&self) -> bool {
        match &self.kind {
            ExprKind::Arith { op, lhs, rhs } => {
                let here = (matches!(op, ArithOp::RealDiv | ArithOp::IntDiv | ArithOp::IntMod))
                    && !rhs.is_constant();
                here || lhs.has_nonconst_divisor() || rhs.has_nonconst_divisor()
            }
            ExprKind::Bv { lhs, rhs, .. } => {
                lhs.has_nonconst_divisor() || rhs.has_nonconst_divisor()
            }
            ExprKind::Neg(a)
            | ExprKind::StrLen(a)
            | ExprKind::ToReal(a)
            | ExprKind::Bv2Int(a) => a.has_nonconst_divisor(),
            ExprKind::Int2Bv { value, .. } => value.has_nonconst_divisor(),
            _ => false,
        }
    }

    /// 全部**分母表达式**（`ALG-2` 的原始收集，未展开）。
    pub fn collect_divisors(&self, out: &mut Vec<Expr>) {
        match &self.kind {
            ExprKind::Arith { op, lhs, rhs } => {
                if op.is_div_like() {
                    out.push((**rhs).clone());
                }
                lhs.collect_divisors(out);
                rhs.collect_divisors(out);
            }
            ExprKind::Bv { lhs, rhs, .. } => {
                lhs.collect_divisors(out);
                rhs.collect_divisors(out);
            }
            ExprKind::Neg(a)
            | ExprKind::StrLen(a)
            | ExprKind::ToReal(a)
            | ExprKind::Bv2Int(a) => a.collect_divisors(out),
            ExprKind::Int2Bv { value, .. } => value.collect_divisors(out),
            _ => {}
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 比较与原子
// ─────────────────────────────────────────────────────────────────────────────

/// 比较运算符（`04 §2` 的 `cmp_op`）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    StrLt,
    StrLe,
}

impl CmpOp {
    pub fn symbol(self) -> &'static str {
        match self {
            CmpOp::Eq => "==",
            CmpOp::Ne => "!=",
            CmpOp::Lt => "<",
            CmpOp::Le => "<=",
            CmpOp::Gt => ">",
            CmpOp::Ge => ">=",
            CmpOp::StrLt => "str.<",
            CmpOp::StrLe => "str.<=",
        }
    }

    /// 不等号反转（`TH-4` 除法线性化 D4/D5 的不等号反转，`03 §3.11.3`）。
    pub fn flip(self) -> Self {
        match self {
            CmpOp::Lt => CmpOp::Gt,
            CmpOp::Le => CmpOp::Ge,
            CmpOp::Gt => CmpOp::Lt,
            CmpOp::Ge => CmpOp::Le,
            other => other,
        }
    }

    /// **两侧互换**后的等价比较符：`a ⋈ b` ⟺ `b reverse(⋈) a`。
    ///
    /// `str.<`/`str.<=` 在 SMT-LIB 中无对应的「反向」算符，故按原样返回
    /// （除法线性化 `D5` 只作用于数值比较，字符串排序不涉及除法）。
    pub fn reverse(self) -> Self {
        match self {
            CmpOp::Lt => CmpOp::Gt,
            CmpOp::Le => CmpOp::Ge,
            CmpOp::Gt => CmpOp::Lt,
            CmpOp::Ge => CmpOp::Le,
            other => other,
        }
    }

    pub fn is_ordering(self) -> bool {
        matches!(
            self,
            CmpOp::Lt | CmpOp::Le | CmpOp::Gt | CmpOp::Ge | CmpOp::StrLt | CmpOp::StrLe
        )
    }
}

/// 原子命题。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Atom {
    /// `lhs cmp rhs`
    Cmp { lhs: Expr, op: CmpOp, rhs: Expr },
    /// 纯布尔表达式上升为公式（`T-BOOL-ATOM`，修正 `B-2`）。
    Bool(Expr),
}

/// CIDR 字面量（`03 §3.12.3`）。
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Cidr {
    /// 地址位宽：32（IPv4）或 128（IPv6）。
    pub width: u32,
    /// 网络地址（大端解释为无符号整数）。
    pub net0: u128,
    /// 前缀长度 `p ∈ [0, width]`。
    pub prefix: u32,
    /// 源码原样文本（用于诊断与反例展示）。
    pub text: String,
}

impl Cidr {
    /// 掩码 `mask(p) = 2ⁿ − 2^(n−p)`（`TH-5`，`03 §3.12.2`）。
    pub fn mask(&self) -> u128 {
        let n = self.width;
        let p = self.prefix;
        if p == 0 {
            0
        } else {
            let full = if n >= 128 { u128::MAX } else { (1u128 << n) - 1 };
            let host = if n - p >= 128 { 0 } else { (1u128 << (n - p)) - 1 };
            full & !host
        }
    }
}

/// 公式的语法节点。`And`/`Or` 采用**列表形式**，与 Lean 侧右结合二元 `conj`/`disj` 同构（`12 §12.5.1 LD-3`）。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FormulaKind {
    True,
    False,
    Atom(Atom),
    Not(Box<Formula>),
    /// 合取；空列表 ≡ `⊤`（`⋀∅ = ⊤`，`03 §3.5.3`）。
    And(Vec<Formula>),
    /// 析取；空列表 ≡ `⊥`（`⋁∅ = ⊥`）。
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    /// `iff`（最低优先级，修正 `B-3`）。
    Iff(Box<Formula>, Box<Formula>),
    /// 有界全称量词；`distinct = true` 时为单射枚举（`Inj`）。
    Forall {
        vars: Vec<String>,
        domain: String,
        distinct: bool,
        body: Box<Formula>,
    },
    /// 有界存在量词。
    Exists {
        vars: Vec<String>,
        domain: String,
        distinct: bool,
        body: Box<Formula>,
    },
    /// `e matches_all [r₁, …, r_k]` → `re.inter`（`TH-6`，`03 §3.13`）。
    MatchesAll {
        subject: Expr,
        patterns: Vec<String>,
    },
    /// `in_cidr(e, "a.b.c.d/p")` → `bvand`（`TH-5`）。
    InCidr { subject: Expr, cidr: Cidr },
    /// `in_range(e, "lo", "hi")` → `(and (bvule lo e) (bvule e hi))`。
    InRange {
        subject: Expr,
        lo: String,
        hi: String,
        width: u32,
        lo_val: u128,
        hi_val: u128,
    },
    /// `unique(D, f)` → `⋀_{i<j} f_i ≠ f_j`（`T-UNIQUE`）。
    Unique { domain: String, field: String },
}

/// 带跨度的公式。
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Formula {
    pub kind: FormulaKind,
    pub span: Span,
}

impl Formula {
    pub fn new(kind: FormulaKind, span: Span) -> Self {
        Formula { kind, span }
    }

    pub fn tru(span: Span) -> Self {
        Formula::new(FormulaKind::True, span)
    }

    pub fn fals(span: Span) -> Self {
        Formula::new(FormulaKind::False, span)
    }

    /// 合取折叠；`[] → ⊤`（`⋀∅ = ⊤`）。
    pub fn and(mut items: Vec<Formula>, span: Span) -> Self {
        if items.is_empty() {
            return Formula::tru(span);
        }
        if items.len() == 1 {
            return items.pop().unwrap();
        }
        Formula::new(FormulaKind::And(items), span)
    }

    /// 析取折叠；`[] → ⊥`（`⋁∅ = ⊥`）。
    pub fn or(mut items: Vec<Formula>, span: Span) -> Self {
        if items.is_empty() {
            return Formula::fals(span);
        }
        if items.len() == 1 {
            return items.pop().unwrap();
        }
        Formula::new(FormulaKind::Or(items), span)
    }

    /// 是否**无量词**（`INV-G` / `TH-2`）。
    pub fn is_quantifier_free(&self) -> bool {
        match &self.kind {
            FormulaKind::True | FormulaKind::False => true,
            FormulaKind::Atom(_) => true,
            FormulaKind::Not(f) => f.is_quantifier_free(),
            FormulaKind::And(fs) | FormulaKind::Or(fs) => fs.iter().all(|f| f.is_quantifier_free()),
            FormulaKind::Implies(a, b) | FormulaKind::Iff(a, b) => {
                a.is_quantifier_free() && b.is_quantifier_free()
            }
            FormulaKind::Forall { .. } | FormulaKind::Exists { .. } => false,
            FormulaKind::MatchesAll { .. }
            | FormulaKind::InCidr { .. }
            | FormulaKind::InRange { .. }
            | FormulaKind::Unique { .. } => true,
        }
    }

    /// 是否存在量词（用于 `INV-G` 断言）。
    pub fn has_quantifier(&self) -> bool {
        !self.is_quantifier_free()
    }

    /// `name` 是否在本公式中作为域实例出现（供 `ALG-1` 死变量剪枝与 `W11` 度量）。
    pub fn occurs_instance(&self, name: &str) -> bool {
        match &self.kind {
            FormulaKind::True | FormulaKind::False => false,
            FormulaKind::Atom(a) => match a {
                Atom::Cmp { lhs, rhs, .. } => {
                    lhs.occurs_instance(name) || rhs.occurs_instance(name)
                }
                Atom::Bool(e) => e.occurs_instance(name),
            },
            FormulaKind::Not(x) => x.occurs_instance(name),
            FormulaKind::And(v) | FormulaKind::Or(v) => {
                v.iter().any(|x| x.occurs_instance(name))
            }
            FormulaKind::Implies(a, b) | FormulaKind::Iff(a, b) => {
                a.occurs_instance(name) || b.occurs_instance(name)
            }
            FormulaKind::Forall { body, .. } | FormulaKind::Exists { body, .. } => {
                body.occurs_instance(name)
            }
            FormulaKind::MatchesAll { subject, .. } => subject.occurs_instance(name),
            FormulaKind::InCidr { subject, .. } => subject.occurs_instance(name),
            FormulaKind::InRange { subject, .. } => subject.occurs_instance(name),
            FormulaKind::Unique { .. } => false,
        }
    }

    /// 收集全部分母表达式（`ALG-2`）。
    pub fn collect_divisors(&self, out: &mut Vec<Expr>) {
        match &self.kind {
            FormulaKind::True | FormulaKind::False => {}
            FormulaKind::Atom(a) => match a {
                Atom::Cmp { lhs, rhs, .. } => {
                    lhs.collect_divisors(out);
                    rhs.collect_divisors(out);
                }
                Atom::Bool(e) => e.collect_divisors(out),
            },
            FormulaKind::Not(x) => x.collect_divisors(out),
            FormulaKind::And(v) | FormulaKind::Or(v) => {
                for x in v {
                    x.collect_divisors(out);
                }
            }
            FormulaKind::Implies(a, b) | FormulaKind::Iff(a, b) => {
                a.collect_divisors(out);
                b.collect_divisors(out);
            }
            FormulaKind::Forall { body, .. } | FormulaKind::Exists { body, .. } => {
                body.collect_divisors(out)
            }
            FormulaKind::MatchesAll { subject, .. } => subject.collect_divisors(out),
            FormulaKind::InCidr { subject, .. } => subject.collect_divisors(out),
            FormulaKind::InRange { subject, .. } => subject.collect_divisors(out),
            FormulaKind::Unique { .. } => {}
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 正则子语言 RegLan（03 §3.13，TH-6）
// ─────────────────────────────────────────────────────────────────────────────

/// SMT-LIB `RegLan` 排序的抽象语法（`τ` 映射的像，`03 §3.13.1`）。
///
/// 与 Lean 侧 `PolicylangProof/Regex.lean` 的 `Re` **一一对应**（`12 §12.5.1`）。
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RegLan {
    /// 任意单字符（`re.allchar`）。
    AllChar,
    /// 全部字串（`Σ*`，发射为 `(re.* re.allchar)`）。
    All,
    /// 空语言（`re.none`）。
    Empty,
    /// 精确字串（`(str.to_re "…")`）。
    Str(String),
    /// 字符区间（`(re.range "a" "z")`）。
    Range(char, char),
    /// 连接（`re.++`）；空序列 ≡ `ε`。
    Concat(Vec<RegLan>),
    /// 并（`re.union`）；空序列 ≡ ∅。
    Union(Vec<RegLan>),
    /// 交（`re.inter`）；空序列 ≡ `Σ*`。
    Inter(Vec<RegLan>),
    Star(Box<RegLan>),
    Plus(Box<RegLan>),
    Opt(Box<RegLan>),
    /// `re.loop`：`{m,n}`（`n = None` 表示无上界）。
    Loop(Box<RegLan>, u32, Option<u32>),
    /// 补（`re.comp`）。
    Complement(Box<RegLan>),
}

/// SMT-LIB 字串字面量的转义规则（`06 §6.2.3`）：仅 `"` 需写成 `""`，不使用反斜杠转义。
pub fn smt_string_literal(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        if c == '"' {
            out.push('"');
            out.push('"');
        } else {
            out.push(c);
        }
    }
    out.push('"');
    out
}

impl RegLan {
    /// `τ` 的发射端：转为 SMT-LIB2 的 `RegLan` 项。
    pub fn to_smt(&self) -> String {
        match self {
            RegLan::AllChar => "re.allchar".to_string(),
            RegLan::All => "(re.* re.allchar)".to_string(),
            RegLan::Empty => "re.none".to_string(),
            RegLan::Str(s) => format!("(str.to_re {})", smt_string_literal(s)),
            RegLan::Range(a, b) => format!(
                "(re.range {} {})",
                smt_string_literal(&a.to_string()),
                smt_string_literal(&b.to_string())
            ),
            RegLan::Concat(v) => {
                if v.is_empty() {
                    "(str.to_re \"\")".to_string()
                } else if v.len() == 1 {
                    v[0].to_smt()
                } else {
                    format!(
                        "(re.++ {})",
                        v.iter().map(RegLan::to_smt).collect::<Vec<_>>().join(" ")
                    )
                }
            }
            RegLan::Union(v) => {
                if v.is_empty() {
                    "re.none".to_string()
                } else if v.len() == 1 {
                    v[0].to_smt()
                } else {
                    format!(
                        "(re.union {})",
                        v.iter().map(RegLan::to_smt).collect::<Vec<_>>().join(" ")
                    )
                }
            }
            RegLan::Inter(v) => {
                if v.is_empty() {
                    "(re.* re.allchar)".to_string()
                } else if v.len() == 1 {
                    v[0].to_smt()
                } else {
                    format!(
                        "(re.inter {})",
                        v.iter().map(RegLan::to_smt).collect::<Vec<_>>().join(" ")
                    )
                }
            }
            RegLan::Star(r) => format!("(re.* {})", r.to_smt()),
            RegLan::Plus(r) => format!("(re.+ {})", r.to_smt()),
            RegLan::Opt(r) => format!("(re.opt {})", r.to_smt()),
            RegLan::Loop(r, m, n) => match n {
                Some(k) => format!("((_ re.loop {m} {k}) {})", r.to_smt()),
                None => format!("(re.++ ((_ re.loop {m} {m}) {}) (re.* {}))", r.to_smt(), r.to_smt()),
            },
            RegLan::Complement(r) => format!("(re.comp {})", r.to_smt()),
        }
    }

    /// 结构规模（用于 `E-REGEX-BUDGET`：`n · |τ(r)| ≤ 4096` 的 `|τ(r)|`）。
    pub fn size(&self) -> u64 {
        match self {
            RegLan::AllChar | RegLan::All | RegLan::Empty => 1,
            RegLan::Str(s) => 1 + s.chars().count() as u64,
            RegLan::Range(..) => 1,
            RegLan::Concat(v) | RegLan::Union(v) | RegLan::Inter(v) => {
                1 + v.iter().map(RegLan::size).sum::<u64>()
            }
            RegLan::Star(r)
            | RegLan::Plus(r)
            | RegLan::Opt(r)
            | RegLan::Complement(r)
            | RegLan::Loop(r, _, _) => 1 + r.size(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reglan_to_smt_and_size() {
        let any = || RegLan::Star(Box::new(RegLan::AllChar));
        let star = RegLan::Concat(vec![any(), RegLan::Range('A', 'Z'), any()]);
        assert_eq!(
            star.to_smt(),
            "(re.++ (re.* re.allchar) (re.range \"A\" \"Z\") (re.* re.allchar))"
        );
        let inter = RegLan::Inter(vec![
            RegLan::Concat(vec![RegLan::Str("A".into()), any()]),
            RegLan::Concat(vec![any(), RegLan::Range('0', '9')]),
        ]);
        assert!(inter.to_smt().starts_with("(re.inter "));
        assert!(star.size() >= 4);
        assert_eq!(smt_string_literal("a\"b"), "\"a\"\"b\"");
        assert_eq!(RegLan::Concat(vec![]).to_smt(), "(str.to_re \"\")");
        assert_eq!(RegLan::Inter(vec![]).to_smt(), "(re.* re.allchar)");
        assert_eq!(RegLan::Union(vec![]).to_smt(), "re.none");
    }

    #[test]
    fn rational_normalizes_and_rejects_zero_denominator() {
        assert_eq!(Rational::new(2, 4).unwrap(), Rational { num: 1, den: 2 });
        assert_eq!(Rational::new(-1, -2).unwrap(), Rational { num: 1, den: 2 });
        assert_eq!(Rational::new(1, -2).unwrap(), Rational { num: -1, den: 2 });
        assert!(Rational::new(1, 0).is_none());
    }

    #[test]
    fn rational_parses_decimal_exactly() {
        // 0.1 必须精确表示为 1/10（f64 无法做到，这是 C-6 的核心动机）。
        assert_eq!(Rational::parse_decimal("0.1").unwrap(), Rational { num: 1, den: 10 });
        assert_eq!(Rational::parse_decimal("-2.25").unwrap(), Rational { num: -9, den: 4 });
        assert_eq!(Rational::parse_decimal("7").unwrap(), Rational { num: 7, den: 1 });
    }

    #[test]
    fn cmp_flip_reverses_ordering_only() {
        assert_eq!(CmpOp::Lt.flip(), CmpOp::Gt);
        assert_eq!(CmpOp::Le.flip(), CmpOp::Ge);
        assert_eq!(CmpOp::Eq.flip(), CmpOp::Eq);
        assert_eq!(CmpOp::Ne.flip(), CmpOp::Ne);
    }

    #[test]
    fn cidr_mask_formula() {
        let c = Cidr {
            width: 32,
            net0: 0x0A000100,
            prefix: 24,
            text: "10.0.1.0/24".into(),
        };
        assert_eq!(c.mask(), 0xFFFFFF00);
        let p0 = Cidr {
            width: 32,
            net0: 0,
            prefix: 0,
            text: "0.0.0.0/0".into(),
        };
        assert_eq!(p0.mask(), 0);
        let p32 = Cidr {
            width: 32,
            net0: 0xFFFFFFFF,
            prefix: 32,
            text: "255.255.255.255/32".into(),
        };
        assert_eq!(p32.mask(), 0xFFFF_FFFF);
    }

    #[test]
    fn empty_and_is_true_empty_or_is_false() {
        let s = Span::new(1, 1, 1, 1);
        assert!(matches!(Formula::and(vec![], s).kind, FormulaKind::True));
        assert!(matches!(Formula::or(vec![], s).kind, FormulaKind::False));
    }
}
