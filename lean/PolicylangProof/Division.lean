/-
  PolicyLang Meta — 除法线性化（定理 TH-4）与 floor 除法不可线性化（命题 3.11.1）
  对应规范：docs/03-形式化语义与可判定性规范.md §3.11.3、§3.11.4

  背景（规范 §3.11.1）：
  SMT-LIB 的 `Real` 除法 `/` 与 `Int` 的 `div`/`mod` 都是**全函数**，
  在除数为 0 时**取值未被指定**（unspecified）。因此若分母可能取 0，
  含除法的比较式可能被求解器任意判真/判假，任何基于它的 PASS 都可能是假证明。
  这就是「除法全域性义务」必须被独立验证的数学理由（`ALG-2`，规范 §3.11.2）。

  在义务 `b ≠ 0` 已被独立解除之后，`/` 可被等价改写为无除法形式（TH-4）。
-/

import PolicylangProof.Syntax

namespace Policylang.Division

/-- 定理 TH-4 (D3)（规范 §3.11.3）：`a / b < c` 的交叉相乘等价。
    不等号在 `b < 0` 时反向，故右式为两情形的析取。

    **Lean 证明计划**：把 `Rat` 视作有序域，按以下 Mathlib 引理逐步改写：
    * `div_lt_iff₀      : 0 < c → (a / c < b ↔ a < b * c)`
    * `lt_div_iff₀      : 0 < c → (a < b / c ↔ a * c < b)`
    * `div_lt_iff_of_neg : c < 0 → (a / c < b ↔ b * c < a)`
    * `lt_div_iff_of_neg : c < 0 → (a < b / c ↔ b < a * c)`
    再对 `b` 用 `lt_trichotomy`（`lt_or_gt_of_ne` + `hb`）分 `0 < b` 与 `b < 0` 两种情形，
    每支用上述引理之一直接化简。
    本工程刻意不依赖 Mathlib（见 `12 §12.2` 的依赖策略），故此处保留 `sorry`。 -/
theorem div_lt_iff (a b c : Rat) (hb : b ≠ 0) :
    a / b < c ↔ (0 < b ∧ a < b * c) ∨ (b < 0 ∧ b * c < a) := by
  sorry

/-- 定理 TH-4 (D1)（规范 §3.11.3）：`a / b = c ⟺ a = b · c`（`b ≠ 0`）。 -/
theorem div_eq_iff (a b c : Rat) (hb : b ≠ 0) : a / b = c ↔ a = b * c := by
  sorry

/-- 定理 TH-4 (D2)：`a / b ≠ c ⟺ a ≠ b · c`（`b ≠ 0`）。 -/
theorem div_ne_iff (a b c : Rat) (hb : b ≠ 0) : a / b ≠ c ↔ a ≠ b * c := by
  rw [div_eq_iff a b c hb]

/-- 定理 TH-4 (D4)：`a / b ≤ c`。 -/
theorem div_le_iff (a b c : Rat) (hb : b ≠ 0) :
    a / b ≤ c ↔ (0 < b ∧ a ≤ b * c) ∨ (b < 0 ∧ b * c ≤ a) := by
  sorry

/-- 定理 TH-4 (D5)：`a / b > c`。 -/
theorem div_gt_iff (a b c : Rat) (hb : b ≠ 0) :
    a / b > c ↔ (0 < b ∧ a > b * c) ∨ (b < 0 ∧ b * c > a) := by
  sorry

/-- 定理 TH-4 (D6)：`a / b ≥ c`。 -/
theorem div_ge_iff (a b c : Rat) (hb : b ≠ 0) :
    a / b ≥ c ↔ (0 < b ∧ a ≥ b * c) ∨ (b < 0 ∧ b * c ≥ a) := by
  sorry

/-- **命题 3.11.1（floor 除法不可线性化，规范 §3.11.4）**

    对整数 `div`/`mod`（floor 语义），不存在仅用 `+`、`-`、常量乘与线性关系
    表达的等价重写。因此实现层（`03 §3.11.4`）采取如下策略：
    * 常量除数 `c ≠ 0`：允许，直接编码 `(div a c)`（须由 `ALG-3` 能力探测确认）；
    * 变量除数：编译期阻断 `E-NONLINEAR`。

    **Lean 证明计划**：反证。设存在线性重写 `L(a, c)`；取 `c = 2`，
    则 `a ↦ ⌊a/2⌋` 的图像在 `a ∈ {0,1,2,3}` 上取 `0,0,1,1`，
    而任何 Presburger 可定义的 `L(·,2)` 在 `a` 上的增长是**逐段等差**的，
    与此阶梯函数在上界处的不一致（可用 `omega` 对 `4 | 5` 的取整差异构造反例）
    矛盾。此处仅冻结命题陈述，机械化留待 `M-6`（见 `12 §12.6`）。 -/
theorem floor_div_not_linearizable :
    ¬ ∃ L : Int → Int,
        (∀ a : Int, L a = Int.ediv a 2) ∧
        (∀ a : Int, L (a + 2) = L a + 1) := by
  sorry

end Policylang.Division
