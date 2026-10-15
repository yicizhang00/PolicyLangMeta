/-
  PolicyLang Meta — 抽象语法（Formal Syntax）
  对应规范：docs/03-形式化语义与可判定性规范.md §3.2、§3.3、§3.4

  设计原则（重要）：
  1. 本模块只刻画 **语法**，不含任何值的表示。
     值域与原子谓词的语义由 Semantics.lean 以「参数」形式提供（`AtomEval`）。
     理由：TH-1（Grounding 保持定理）与 TH-2（量词消除）只依赖语法结构
     与环境重命名，与算术 / 位运算 / 字符串的具体解释无关。
  2. 结构体一律**不携带证明字段**，良构性（W1–W12）以独立谓词给出，
     以避免 `deriving Repr` 与 Prop 字段冲突。
  3. **合取 / 析取取右结合二元形式**（`conj` / `disj`）而非列表，理由是
     使 `Formula` 成为**非嵌套**归纳类型，从而 `induction` 产生可用的归纳假设。
     实现层的 n 元 `Formula::And(Vec<Formula>)` 与本文的 `conjsOf` 同构，
     该同构及其语义等价性见 `12 §12.5` 的「AST 一致性契约」。
-/

namespace Policylang

/-- 标量排序（规范 §3.2.1） -/
inductive Sort where
  /-- 整数，必须配 `[min:a, max:b]`（`W2`） -/
  | int
  /-- 实数，以**精确有理数**为模型（规范 §3.2.3 `N-1`） -/
  | real
  /-- 布尔，天然有界 -/
  | bool
  /-- 字符串（Unicode 码点序列） -/
  | str
  /-- 定长位向量 -/
  | bv (width : Nat)
  /-- 枚举，成员数 `card ≥ 1` -/
  | enum (card : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- 域声明（规范定义 3.2.2）：索引集为 `Fin size` -/
structure Domain where
  /-- 域名 -/
  name   : String
  /-- 所依赖的实体名 -/
  entity : String
  /-- 实例数 `N` -/
  size   : Nat
  deriving Repr, DecidableEq, Inhabited

/-- 域良构性（规范 `W3`）：`N ≥ 1` -/
def Domain.WF (d : Domain) : Prop := 0 < d.size

/-- 实例引用 `(D, i)`（规范定义 3.2.3） -/
structure Instance where
  /-- 域名 -/
  domain : String
  /-- 实例索引 -/
  index  : Nat
  deriving Repr, DecidableEq, Inhabited

/-- 算术与位运算算子（规范 §3.5.1） -/
inductive ArithOp where
  | add | sub | mul | div | idiv | imod | bvand
  deriving Repr, DecidableEq, Inhabited

/-- 比较算子 -/
inductive CmpOp where
  | eq | ne | lt | le | gt | ge
  deriving Repr, DecidableEq, Inhabited

/-- 项（规范 §3.5.1） -/
inductive Term where
  /-- 全局变量 `v` -/
  | gvar        : String → Term
  /-- 量化绑定变量的字段访问 `x.f` -/
  | fieldAccess : String → String → Term
  /-- 展平标量 `D_i_f`（规范 §3.2.4 的 `scalar_symbol`） -/
  | flat        : Instance → String → Term
  /-- 整数字面量 -/
  | iLit        : Int → Term
  /-- 有理数字面量 `num/den`（`den ≠ 0`） -/
  | rLit        : Int → Int → Term
  /-- 布尔字面量 -/
  | bLit        : Bool → Term
  /-- 字符串字面量（Unicode 码点序列） -/
  | sLit        : List Nat → Term
  /-- 位向量字面量（位宽、值） -/
  | bvLit       : Nat → Nat → Term
  /-- 二元运算 -/
  | binop       : ArithOp → Term → Term → Term
  /-- 字符串长度 `str.len` -/
  | strLen      : Term → Term
  deriving Repr, DecidableEq, Inhabited

/-- CIDR 字面量（规范 §3.12.1） -/
structure Cidr where
  /-- 地址位宽 `n`（IPv4 为 32，IPv6 为 128） -/
  width  : Nat
  /-- 网络号 `n₀` -/
  net0   : Nat
  /-- 前缀长度 `p` -/
  prefix : Nat
  deriving Repr, DecidableEq, Inhabited

/-- CIDR 良构性：`p ≤ n` 且 `n₀ < 2ⁿ` -/
def Cidr.WF (c : Cidr) : Prop := c.prefix ≤ c.width ∧ c.net0 < 2 ^ c.width

/-- SMT-LIB 2.6 `RegLan` 理论的正则表达式（规范 §3.13.1 的转译目标） -/
inductive RegLan where
  /-- `(str.to_re w)`：字面码点序列 -/
  | toRe   : List Nat → RegLan
  /-- `re.allchar`：任意单码点 -/
  | allchar : RegLan
  /-- `(re.range a b)`：码点区间 -/
  | range  : Nat → Nat → RegLan
  /-- `(re.union r s)` -/
  | union  : RegLan → RegLan → RegLan
  /-- `(re.inter r s)` -/
  | inter  : RegLan → RegLan → RegLan
  /-- `(re.concat r s)` -/
  | concat : RegLan → RegLan → RegLan
  /-- `(re.comp r)` -/
  | comp   : RegLan → RegLan
  /-- `(re.* r)` -/
  | star   : RegLan → RegLan
  /-- `(re.+ r)` -/
  | plus   : RegLan → RegLan
  /-- `(re.opt r)` -/
  | opt    : RegLan → RegLan
  deriving Repr, DecidableEq, Inhabited

/-- 原子谓词：规范 §3.5.2 中除逻辑联结词与量词以外的全部公式形态。
    其语义由外部解释器 `AtomEval` 提供，从而把「算术 / 位运算 / 字符串的解释」
    与「Grounding 变换的正确性」两件事解耦。 -/
inductive Atom where
  /-- `a R b` -/
  | cmp        : Term → CmpOp → Term → Atom
  /-- `x in [a..b]` -/
  | inRange    : Term → Term → Term → Atom
  /-- `unique(D, f)` -/
  | unique     : String → String → Atom
  /-- `e matches_all [r̄]` -/
  | matchesAll : Term → List RegLan → Atom
  /-- `in_cidr(e, c)` -/
  | inCidr     : Term → Cidr → Atom
  /-- 裸布尔表达式（规范 §3.4.3 补全项 `B-2` 的 `bool_atom`） -/
  | boolAtom   : Term → Atom
  deriving Repr, DecidableEq, Inhabited

/-- 公式（规范 §3.5.2）。合取 / 析取为右结合二元形式，见文件头说明 3。 -/
inductive Formula where
  /-- 真 `⊤` -/
  | tt
  /-- 假 `⊥` -/
  | ff
  /-- 原子谓词 -/
  | atom    : Atom → Formula
  /-- 合取 `φ ∧ ψ` -/
  | conj    : Formula → Formula → Formula
  /-- 析取 `φ ∨ ψ` -/
  | disj    : Formula → Formula → Formula
  /-- 否定 `¬φ` -/
  | neg     : Formula → Formula
  /-- 蕴含 `φ ⟹ ψ` -/
  | impl    : Formula → Formula → Formula
  /-- 等价 `φ ⟺ ψ`（规范 §3.4.3 补全项 `B-3`） -/
  | biff    : Formula → Formula → Formula
  /-- 有界全称量词：变量组、域、是否单射、体 -/
  | qall    : List String → String → Bool → Formula → Formula
  /-- 有界存在量词：变量组、域、是否单射、体 -/
  | qex     : List String → String → Bool → Formula → Formula
  deriving Repr

end Policylang
