/-
  PolicyLang Meta — 指称语义（Denotational Semantics）
  对应规范：docs/03-形式化语义与可判定性规范.md §3.5

  设计原则：
  * 语义只需提供两件事——「域规模」与「原子谓词解释器」。
    展平标量、全局变量的值域与算术解释完全归属于 `AtomEval`，
    因此本文件的定理与算术 / 位运算 / 字符串的具体理论无关。
  * 量词按**界谓词**解释（而非按枚举折叠）。这是刻意的：
    只有这样，「TH-1：ground 保持语义」才是有内容的定理，
    而不是把实现当作自己的规格。
-/

import PolicylangProof.Syntax

namespace Policylang

/-- 结构 `M`：规范 §3.2.5 中 `m ∈ M` 的抽象。
    本层只需「域规模」；具体标量取值由 `AtomEval` 承担。 -/
structure Model where
  /-- 域规模查询 `N_D = |idx(D)|` -/
  domSize : String → Nat
  deriving Repr

/-- 绑定环境 `Σ`：量化变量 → 实例（规范 §3.6.2）。
    取为**全函数**以避免 `Option` 在证明中引入无关分支；
    良构性 `W5`/`W6` 保证被访问的变量确实已被绑定。 -/
abbrev Env := String → Instance

/-- 缺省环境（仅当良构性被破坏时才可能被观测到） -/
def Env.base : Env := fun _ => ⟨"", 0⟩

/-- 单变量绑定 `Σ[x ↦ i]` -/
def Env.bind (ρ : Env) (x : String) (i : Instance) : Env :=
  fun y => if y = x then i else ρ y

/-- 变量组绑定：把 `vars` 与索引列表 `is` 逐位配对后绑定
    （规范 §3.6.1 的 `Σ[x̄ ↦ (D, ī)]`）。
    用 `zip` + `foldl` 实现，以避免自定义结构递归的终止性证明负担。 -/
def Env.bindAll (ρ : Env) (dom : String) (vars : List String) (is : List Nat) : Env :=
  (vars.zip is).foldl (fun acc p => Env.bind acc p.1 ⟨dom, p.2⟩) ρ

/-- 原子解释器：由语义模型提供。
    它承担规范 §3.5.2 中 `cmp`/`inRange`/`unique`/`matchesAll`/`inCidr`/`boolAtom`
    各条款以及 §3.5.1 的全部项语义。 -/
abbrev AtomEval := Env → Atom → Prop

/-- 公式语义（规范 §3.5.2）。

    量词条款按**界谓词**给出：
    * 变量组绑定到一个长度等于变量数的索引列表 `is`；
    * `is` 的每个元素必须落在域内（`i < N`）；
    * 若 `distinct = true`，额外要求 `is.Nodup`（规范 §3.5.2 的 `Inj`）；
      若 `distinct = false`，该要求为建材蕴含（前提为假），即全笛卡尔积
      （规范公理 `AX-Q-INDEP`）。 -/
def eval (E : AtomEval) (M : Model) (ρ : Env) : Formula → Prop
  | .tt            => True
  | .ff            => False
  | .atom a        => E ρ a
  | .conj a b      => eval E M ρ a ∧ eval E M ρ b
  | .disj a b      => eval E M ρ a ∨ eval E M ρ b
  | .neg f         => ¬ eval E M ρ f
  | .impl a b      => eval E M ρ a → eval E M ρ b
  | .biff a b      => (eval E M ρ a ↔ eval E M ρ b)
  | .qall vars dom distinct body =>
      ∀ is : List Nat,
        is.length = vars.length →
        (∀ i ∈ is, i < M.domSize dom) →
        (distinct = true → is.Nodup) →
        eval E M (ρ.bindAll dom vars is) body
  | .qex vars dom distinct body =>
      ∃ is : List Nat,
        is.length = vars.length ∧
        (∀ i ∈ is, i < M.domSize dom) ∧
        (distinct = true → is.Nodup) ∧
        eval E M (ρ.bindAll dom vars is) body

end Policylang
