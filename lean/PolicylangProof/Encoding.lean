/-
  PolicyLang Meta — 编码充分性（定理 TH-7）
  对应规范：docs/03-形式化语义与可判定性规范.md §3.14
           docs/06-SMT编码与求解编排规范.md §6.3

  本模块把「SMT-LIB2 查询的判定结果」与「验证目标的数学命题」之间的
  等价关系固化为 Lean 定理陈述，是 §6.3 逐式编码论证的机械化目标。

  Lean 侧的关键设计：把「规范」抽象为 `Spec`（策略规则、分支、不变量、
  除零义务的查询），把「查询」抽象为 `Goal.query`（断言列表），
  于是 TH-7 成为「存在满足 `query` 的赋值 ⟺ 该目标的数学命题不成立」。
-/

import PolicylangProof.Grounder
import PolicylangProof.GrounderSoundness

namespace Policylang.Encoding

/-- 规范 `S`：只需承载编码所需的三类构件（规范 §6.3 的 `R_P`、`Br_P`、`Inv`、`obl`） -/
structure Spec where
  /-- 策略的规则集（已展开；键为策略名） -/
  rules      : String → List Formula
  /-- 策略的分支集（`FR-15`；键为策略名） -/
  branches   : String → List Formula
  /-- 策略的第 `i` 个分支（供 `mutex` 逐对取用） -/
  branchAt   : String → Nat → Formula
  /-- 分支个数 -/
  branchCount : String → Nat
  /-- 不变量（键为不变量名） -/
  invariants : String → Formula
  /-- 除零义务的**否定**（`bⱼ = 0`），由 `ALG-2` 从 AST 收集（规范 §3.11.2） -/
  divObl     : String → List Formula

/-- 策略约束的合取 `R_P`（规范 §6.3 记号） -/
def Spec.R (S : Spec) (p : String) : Formula := conjsOf (S.rules p)

/-- 策略分支的析取 `Br_P`（规范 §6.3.4） -/
def Spec.Br (S : Spec) (p : String) : Formula := disjsOf (S.branches p)

/-- 六式验证目标（规范 §3.14 与 `06 §6.3`；`mutex` 逐对编码） -/
inductive Goal where
  /-- 策略集自洽性 -/
  | consistency  (p : String)
  /-- 安全不变量 -/
  | invariant    (inv p : String)
  /-- 策略精化对比 -/
  | refines      (new_ old : String)
  /-- 分支完备性 -/
  | completeness (p : String)
  /-- 分支两两互斥（第 `i`、`j` 对） -/
  | mutex        (p : String) (i j : Nat)
  /-- 除法全域性义务 -/
  | safety       (p : String)
  deriving Repr

/-- 目标的**数学命题** `π`（规范 `TH-7` 中的 `π(V)`） -/
def Goal.pi (S : Spec) (M : Model) (E : AtomEval) : Goal → Prop
  | .consistency p     => ∃ ρ, eval E M ρ (S.R p)
  | .invariant i p     => ∀ ρ, eval E M ρ (S.R p) → eval E M ρ (S.invariants i)
  | .refines n o       => ∀ ρ, eval E M ρ (S.R n) → eval E M ρ (S.R o)
  | .completeness p    => ∀ ρ, eval E M ρ (S.Br p)
  | .mutex p i j       =>
      ∀ ρ, eval E M ρ (S.R p) →
        ¬ (eval E M ρ (S.branchAt p i) ∧ eval E M ρ (S.branchAt p j))
  | .safety p          =>
      ∀ ρ, eval E M ρ (S.R p) → ∀ f ∈ S.divObl p, ¬ eval E M ρ f

/-- 目标的**编码查询** `Q`：断言列表（规范 `TH-7` 中的 `Q(V)`；`06 §6.1.1` 的
    `<goal-asserts>`，边界断言 `Bnd` 已隐含于 `M` 与 `E` 的解释中） -/
def Goal.query (S : Spec) (g : Goal) : List Formula :=
  match g with
  | .consistency p     => S.rules p
  | .invariant i p     => S.R p :: [Formula.neg (S.invariants i)]
  | .refines n o       => S.R n :: [Formula.neg (S.R o)]
  | .completeness p    => [Formula.neg (S.Br p)]
  | .mutex p i j       => [Formula.conj (S.branchAt p i) (S.branchAt p j)]
  | .safety p          => S.R p :: [disjsOf (S.divObl p)]

/-- **定理 TH-7（Encoding Adequacy，规范 §3.14）**

    编码**可靠且相对完备**：`Q` 可满足 ⟺ `π` 不成立。
    由此立即得到规范 §3.14 的三条结论：
    (i) `unsat ⟹ π`；(ii) `sat ⟹ ¬π` 且模型即反例；(iii) `unknown` 不作断言。

    **证明计划**（逐目标展开 `Goal.pi` / `Goal.query`，对应 `06 §6.3` 的逐式表）：
    * `consistency`：两边同为 `∃ ρ, eval (conjsOf (rules p))`，由 `eval_conjsOf` 即得；
    * `invariant` / `refines`：`Q` 为 `[R_P, ¬Inv]`，可满足 ⟺ `∃ρ, eval R_P ∧ ¬eval Inv`，
      再由 `not_forall` 型经典逻辑改写为 `¬∀ρ, eval R_P → eval Inv`；
    * `completeness`：`Q = [¬Br_P]`，可满足 ⟺ `¬∀ρ, eval Br_P`；
    * `safety`：`Q = [R_P, ⋁ (bⱼ = 0)]`，可满足 ⟺ `∃ρ, eval R_P ∧ ∃j, bⱼ(ρ) = 0`，
      即 `¬∀ρ, eval R_P → ⋀ bⱼ ≠ 0`；
    * `mutex`：`Q = [Bᵢ ∧ Bⱼ]`，可满足 ⟺ `∃ρ, Bᵢ ∧ Bⱼ`，即 `¬` 互斥。
    各支均需 `eval_conjsOf` / `eval_disjsOf` 与经典逻辑的德摩根律，
    故本陈述的机械化排在 `M-6`（见 `12 §12.6`）。 -/
theorem encoding_adequate (S : Spec) (M : Model) (E : AtomEval) (g : Goal) :
    (∃ ρ, ∀ f ∈ Goal.query S g, eval E M ρ f) ↔ ¬ Goal.pi S M E g := by
  sorry

/-- **诚实阻断（规范 §3.14 (iii)、`G-8`）**：`unknown` 不产生任何断言。
    以类型层面的「不可导出」固定该语义，杜绝把 `unknown` 当作 PASS 的实现。 -/
inductive Verdict where
  | sat
  | unsat
  | unknown
  deriving Repr, DecidableEq

/-- 由判定结果推出的结论：`unknown` 对应 `True`（零信息）。 -/
def Verdict.conclusion (S : Spec) (M : Model) (E : AtomEval) (g : Goal) : Verdict → Prop
  | .sat     => ¬ Goal.pi S M E g
  | .unsat   => Goal.pi S M E g
  | .unknown => True

end Policylang.Encoding
