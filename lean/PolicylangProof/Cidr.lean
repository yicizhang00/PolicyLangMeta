/-
  PolicyLang Meta — CIDR 掩码等价（定理 TH-5）
  对应规范：docs/03-形式化语义与可判定性规范.md §3.12

  目标：证明「按位与掩码」编码与「高 p 位相等」的集合语义等价，
  从而确认 `in_cidr(e, "A.B.C.D/p")` 的 SMT-LIB2 编码（`06 §6.3`、`04 §10`）可信。
-/

import PolicylangProof.Syntax

namespace Policylang.CidrTheory

/-- 掩码（规范 §3.12.1）：`mask(p) ≜ 2ⁿ − 2^(n−p)`，`mask(0) ≜ 0` -/
def mask (n p : Nat) : Nat :=
  if p = 0 then 0 else 2 ^ n - 2 ^ (n - p)

/-- 清低位操作：`clearlow(n,p,x) ≜ ⌊x / 2^(n−p)⌋ · 2^(n−p)`。
    这是 `bvand` 语义的算术刻画（`x &&& mask(p)`），
    其与 `Nat.land` 的一致性由引理 `clearlow_eq_land` 给出（`sorry`，见下）。 -/
def clearlow (n p x : Nat) : Nat :=
  (x / 2 ^ (n - p)) * 2 ^ (n - p)

/-- 定理 TH-5 的核心（规范 §3.12.2 的证明主干）：
    两个地址在「清低 `n−p` 位」后相等，当且仅当它们的高 `p` 位相等。

    **证明**：设 `d ≜ 2^(n−p)`，`d ≠ 0`。
    * `(⟸)` 若 `x / d = y / d`，两边同乘 `d` 得 `clearlow` 相等（`congrArg`）。
    * `(⟹)` 若 `(x / d) · d = (y / d) · d`，由 `d ≠ 0` 约去 `d` 得 `x / d = y / d`。
    这正是规范 §3.12.2 中「`&&& M = ⌊·/2^s⌋·2^s`」这一步的形式化。 -/
theorem clearlow_eq_iff (n p x y : Nat) (hp : p ≤ n) :
    clearlow n p x = clearlow n p y ↔ x / 2 ^ (n - p) = y / 2 ^ (n - p) := by
  unfold clearlow
  have hd : 2 ^ (n - p) ≠ 0 := Nat.pow_ne_zero _ (by omega)
  constructor
  · intro h
    exact Nat.mul_right_cancel h
  · intro h
    rw [h]

/-- 定理 TH-5 的集合语义侧（规范 §3.12.2）：
    `clearlow` 相等等价于「同属同一 CIDR 块」，
    而 CIDR 块由「高 `p` 位相同」刻画；因此掩码编码与集合成员语义一致。 -/
theorem inCidr_iff_block (n p x net0 : Nat) (hp : p ≤ n) :
    clearlow n p x = clearlow n p net0 ↔ x / 2 ^ (n - p) = net0 / 2 ^ (n - p) :=
  clearlow_eq_iff n p x net0 hp

/-- `clearlow` 与 SMT-LIB `bvand` 语义的一致性（规范 §3.12.3 的编码依据）。

    `x &&& mask(n,p) = ⌊x / 2^(n−p)⌋ · 2^(n−p)` 对 `x < 2ⁿ` 成立。

    **证明计划**：对 `p` 归纳。
    * `p = 0`：`mask = 0`，两边皆为 `0`。
    * `p + 1`：`mask(n,p+1) = 2ⁿ − 2^(n−p−1) = mask(n,p) + 2^(n−p−1)`，
      且 `clearlow(n,p,x) = clearlow(n,p+1,x) + (bit_{n−p−1}(x) · 2^(n−p−1))`，
      逐位相加即得。需 `Nat.land_eq_lor_and_shift` 一族位引理。
    依赖 `Nat` 的位运算引理，故保留 `sorry` 并登记为 `M-6` 的机械化项。 -/
theorem clearlow_eq_land (n p x : Nat) (hx : x < 2 ^ n) (hp : p ≤ n) :
    Nat.land x (mask n p) = clearlow n p x := by
  sorry

/-- **定理 TH-5（CIDR Masking Equivalence，规范 §3.12.2）**

    对满足 `x < 2ⁿ` 的地址 `x` 与网络号 `net₀`，
    `in_cidr` 的掩码编码与其集合语义（同属 `block(net₀, p)`）等价。 -/
theorem inCidr_encoding_correct (n p x net0 : Nat)
    (hx : x < 2 ^ n) (hnet : net0 < 2 ^ n) (hp : p ≤ n) :
    Nat.land x (mask n p) = Nat.land net0 (mask n p) ↔
      x / 2 ^ (n - p) = net0 / 2 ^ (n - p) := by
  rw [clearlow_eq_land n p x hx hp, clearlow_eq_land n p net0 hnet hp]
  exact clearlow_eq_iff n p x net0 hp

end Policylang.CidrTheory
