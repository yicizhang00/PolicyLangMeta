import Lake
open Lake DSL

/-
  PolicyLang Meta — Lean 4 形式化验证工程
  对应规范：docs/12-Lean4形式化验证规范.md

  依赖策略（12 §12.2）：**不引入 Mathlib**。
  理由：本工程的目标是证明「有界量词展开保持语义」「量词消除」「CIDR 掩码等价」
  「正则转译保持语言」「除法线性化」这五类**结构性**命题，其证明只需
  Lean 4 核心库（`Init` + `Std`）的 `List` / `Nat` / `Rat` 引理。
  避免 Mathlib 依赖可把 `lake build` 从「数十分钟 + 数 GB 下载」压到
  「秒级」，从而可以进入每次 PR 的 CI 门禁（12 §12.7）。
  对确需有序域代数 API 的定理（TH-4），本工程以 `sorry` 冻结陈述并
  在 `12 §12.6` 登记为待机械化项，同时给出应采用的 Mathlib 引理清单。
-/

package «policylang-proof»

@[default_target]
lean_lib PolicylangProof
