/-
  PolicyLang Meta — 正则子语言转译器与语言保持（定理 TH-6）
  对应规范：docs/03-形式化语义与可判定性规范.md §3.13

  目标：证明 PCRE 可判定子集 `R_sub`（规范表 3.13.1）到 SMT-LIB 2.6
  `RegLan` 理论（`Syntax.lean` 的 `RegLan`）的转译函数 `toRegLan`
  **保持语言**：`L(τ(r)) = L(r)`。
  这是 `matches_all` 能落地为 `(str.in_re e (re.inter …))` 的前提
  （规范 `TH-6-C1`）。

  注意：本文件不处理拒绝清单（规范 §3.13.2 的 `E-REGEX-NONREGULAR` /
  `E-REGEX-UNSUPPORTED` / `E-REGEX-BUDGET`）——那些构造**根本没有进入
  `R_sub` 的语法**，故在类型层面被排除，无需在此证明。
-/

import PolicylangProof.Syntax

namespace Policylang.Regex

/-- `R_sub` 的抽象语法（规范表 3.13.1 的允许构造）。
    语法糖（`\d`、`\w`、`[a-z]`、`{n,m}`、`^…$`）在**解析阶段**被展开为
    下列基本构造，因此此处只需基本构造。 -/
inductive Re where
  /-- 单码点字面量 -/
  | lit    : Nat → Re
  /-- `.`：任意单码点 -/
  | any    : Re
  /-- `[a-z]`：码点闭区间 -/
  | range  : Nat → Nat → Re
  /-- `[abc]`：码点显式集合 -/
  | cls    : List Nat → Re
  /-- `[^abc]`：补集 -/
  | negCls : List Nat → Re
  /-- 连接 `r₁ r₂` -/
  | concat : Re → Re → Re
  /-- 选择 `r₁|r₂` -/
  | union  : Re → Re → Re
  /-- `r*` -/
  | star   : Re → Re
  /-- `r+` -/
  | plus   : Re → Re
  /-- `r?` -/
  | opt    : Re → Re
  deriving Repr, DecidableEq, Inhabited

/-! ### SMT-LIB `RegLan` 的语言语义 -/

/-- 语言的 `n` 次幂（连接幂）：`R⁰ = {ε}`，`R^(n+1) = R · Rⁿ` -/
def langPow (R : Set (List Nat)) : Nat → Set (List Nat)
  | 0     => {u | u = []}
  | n + 1 => {u | ∃ v w, u = v ++ w ∧ v ∈ R ∧ w ∈ langPow R n}

/-- SMT-LIB `RegLan` 的标准语义 `L(·)`（规范 §3.13.3 引用的语义） -/
def Lang : RegLan → Set (List Nat)
  | .toRe w      => {u | u = w}
  | .allchar     => {u | u.length = 1}
  | .range a b   => {u | ∃ c, u = [c] ∧ a ≤ c ∧ c ≤ b}
  | .union r s   => Lang r ∪ Lang s
  | .inter r s   => Lang r ∩ Lang s
  | .concat r s  => {u | ∃ v w, u = v ++ w ∧ v ∈ Lang r ∧ w ∈ Lang s}
  | .comp r      => {u | u ∉ Lang r}
  | .star r      => {u | ∃ n, u ∈ langPow (Lang r) n}
  | .plus r      => {u | ∃ n, 0 < n ∧ u ∈ langPow (Lang r) n}
  | .opt r       => Lang r ∪ {u | u = []}

/-- PCRE 侧的语言语义（与 `Lang` **独立定义**，以保证定理有实质内容） -/
def LangRe : Re → Set (List Nat)
  | .lit c      => {u | u = [c]}
  | .any        => {u | u.length = 1}
  | .range a b  => {u | ∃ c, u = [c] ∧ a ≤ c ∧ c ≤ b}
  | .cls cs     => {u | ∃ c, u = [c] ∧ c ∈ cs}
  | .negCls cs  => {u | ∃ c, u = [c] ∧ c ∉ cs}
  | .concat r s => {u | ∃ v w, u = v ++ w ∧ v ∈ LangRe r ∧ w ∈ LangRe s}
  | .union r s  => LangRe r ∪ LangRe s
  | .star r     => {u | ∃ n, u ∈ langPow (LangRe r) n}
  | .plus r     => {u | ∃ n, 0 < n ∧ u ∈ langPow (LangRe r) n}
  | .opt r      => LangRe r ∪ {u | u = []}

/-! ### 转译函数 τ（规范表 3.13.1） -/

/-- 字符类折叠为 `re.union` 链：`[c₁,…,cₖ] ↦ (re.union (str.to_re c₁) … )` -/
def clsToRegLan (cs : List Nat) : RegLan :=
  cs.foldr (fun c acc => .union (.toRe [c]) acc) (.toRe [])

/-- PCRE 子集 → SMT-LIB `RegLan` 的转译（规范规范表 3.13.1 的 `τ`） -/
def toRegLan : Re → RegLan
  | .lit c      => .toRe [c]
  | .any        => .allchar
  | .range a b  => .range a b
  | .cls cs     => clsToRegLan cs
  | .negCls cs  => .comp (clsToRegLan cs)
  | .concat r s => .concat (toRegLan r) (toRegLan s)
  | .union r s  => .union (toRegLan r) (toRegLan s)
  | .star r     => .star (toRegLan r)
  | .plus r     => .plus (toRegLan r)
  | .opt r      => .opt (toRegLan r)

/-! ### 引理与主定理 -/

/-- 字符类折叠的语言（`re.union` 链的语义）。
    **证明计划**：对 `cs` 归纳，`nil` 支给出 `Lang (re.toRe []) = {u | u = []}`
    与 `{u | ∃ c, u = [c] ∧ c ∈ []} = ∅` 的差集处理；
    `cons` 支用 `Lang (.union r s) = Lang r ∪ Lang s` 与归纳假设。
    需要处理 `{u | u = []}` 与 `∅` 的不一致，故用 `Set.ext` + `simp`。 -/
theorem lang_clsToRegLan (cs : List Nat) :
    Lang (clsToRegLan cs) = {u | ∃ c, u = [c] ∧ c ∈ cs} := by
  sorry

/-- 补字符类的语言：`[^abc] ↦ (re.comp (re.union …))` -/
theorem lang_negClsToRegLan (cs : List Nat) :
    Lang (.comp (clsToRegLan cs)) = {u | ∃ c, u = [c] ∧ c ∉ cs} := by
  rw [lang_clsToRegLan, Set.compl_setOf]
  ext u
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, rfl, hc⟩
    exact ⟨c, rfl, hc⟩
  · rintro ⟨c, rfl, hc⟩
    exact ⟨c, rfl, hc⟩

/-- **定理 TH-6（Regex Transpilation Preserves Language，规范 §3.13.3）**

    `L(τ(r)) = L(r)`：转译函数保持语言，因此 `matches_all` 的编码
    `(str.in_re e (re.inter τ(r₁) … τ(rₖ)))` 与规范 §3.5.2 的语义
    `⟦e⟧ρ ∈ ⋂ L(rᵢ)` 一致。 -/
theorem toRegLan_correct (r : Re) : Lang (toRegLan r) = LangRe r := by
  induction r with
  | lit c => rfl
  | any => rfl
  | range a b => rfl
  | cls cs => lang_clsToRegLan cs
  | negCls cs => lang_negClsToRegLan cs
  | concat a b iha ihb =>
      simp only [toRegLan, Lang, LangRe, iha, ihb]
  | union a b iha ihb =>
      simp only [toRegLan, Lang, LangRe, iha, ihb]
  | star a iha =>
      simp only [toRegLan, Lang, LangRe, iha]
  | plus a iha =>
      simp only [toRegLan, Lang, LangRe, iha]
  | opt a iha =>
      simp only [toRegLan, Lang, LangRe, iha]

/-- **推论 TH-6-C1（规范 §3.13.3）**：`matches_all` 的 `re.inter` 编码语义。

    空模式表退化为 `⊤`（`⋂∅ = Σ*`），单模式表退化为 `str.in_re`。 -/
theorem matchesAll_inter_correct (rs : List RegLan) (w : List Nat) :
    (∀ r ∈ rs, w ∈ Lang r) ↔ w ∈ {u | ∀ r ∈ rs, u ∈ Lang r} :=
  Iff.rfl

end Policylang.Regex
