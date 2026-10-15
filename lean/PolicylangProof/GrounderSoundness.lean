/-
  PolicyLang Meta — Grounding 正确性（定理 TH-1、TH-1-C2、TH-2）
  对应规范：docs/03-形式化语义与可判定性规范.md §3.7、§3.8

  证明策略（与规范 §3.7 的证明结构逐条对应）：
  * `eval_conjsOf` / `eval_disjsOf`：把右结合二元合取/析取的语义还原为列表上的
    全称/存在量化（对应规范中 `⋀`/`⋁` 的组合性条款）；
  * `forall_mem_map` / `exists_mem_map`：处理 `List.map` 与量化的交换；
  * `mem_tupleFamily`：把「索引列表属于枚举族」等价为规范 §3.5.2 的三条界条件，
    这是量词分支证明的**唯一实质性引理**；
  * `ground_preserves`（TH-1）：对 `φ` 结构归纳，并 `generalizing ρ`
    以便量词分支在**任意**环境上使用归纳假设。
-/

import PolicylangProof.Grounder

namespace Policylang

/-! ## 辅助引理 -/

/-- 列表全称量化与 `List.map` 的交换 -/
theorem forall_mem_map {α : Type} {l : List α} {g : α → Formula} {F : Formula → Prop} :
    (∀ f ∈ l.map g, F f) ↔ ∀ a ∈ l, F (g a) := by
  constructor
  · intro h a ha
    exact h (g a) (List.mem_map.mpr ⟨a, ha, rfl⟩)
  · rintro h _ ⟨a, ha, rfl⟩
    exact h a ha

/-- 列表存在量化与 `List.map` 的交换 -/
theorem exists_mem_map {α : Type} {l : List α} {g : α → Formula} {F : Formula → Prop} :
    (∃ f ∈ l.map g, F f) ↔ ∃ a ∈ l, F (g a) := by
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hF⟩
    exact ⟨a, ha, hF⟩
  · rintro ⟨a, ha, hF⟩
    exact ⟨g a, List.mem_map.mpr ⟨a, ha, rfl⟩, hF⟩

/-- 右结合 n 元合取的语义（规范 §3.5.2 的 `⋀` 组合性；`⋀∅ = ⊤`） -/
theorem eval_conjsOf (E : AtomEval) (M : Model) (ρ : Env) :
    ∀ l : List Formula, eval E M ρ (conjsOf l) ↔ ∀ f ∈ l, eval E M ρ f := by
  intro l
  induction l with
  | nil => simp [conjsOf, eval]
  | cons a as ih =>
      simp only [conjsOf, eval]
      rw [ih]
      constructor
      · rintro ⟨h1, h2⟩ f hf
        rcases List.mem_cons.mp hf with rfl | hf'
        · exact h1
        · exact h2 f hf'
      · intro hf
        exact ⟨hf a (List.mem_cons.mpr (Or.inl rfl)),
               fun f hf' => hf f (List.mem_cons.mpr (Or.inr hf'))⟩

/-- 右结合 n 元析取的语义（`⋁∅ = ⊥`） -/
theorem eval_disjsOf (E : AtomEval) (M : Model) (ρ : Env) :
    ∀ l : List Formula, eval E M ρ (disjsOf l) ↔ ∃ f ∈ l, eval E M ρ f := by
  intro l
  induction l with
  | nil => simp [disjsOf, eval]
  | cons a as ih =>
      simp only [disjsOf, eval]
      rw [ih]
      constructor
      · rintro (h1 | h2)
        · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), h1⟩
        · obtain ⟨f, hf, hF⟩ := h2
          exact ⟨f, List.mem_cons.mpr (Or.inr hf), hF⟩
      · rintro ⟨f, hf, hF⟩
        rcases List.mem_cons.mp hf with rfl | hf'
        · exact Or.inl hF
        · exact Or.inr ⟨f, hf', hF⟩

/-- 无量词的右结合合取（定理 TH-2 的列表侧） -/
theorem isQF_conjsOf : ∀ l : List Formula, IsQF (conjsOf l) ↔ ∀ f ∈ l, IsQF f := by
  intro l
  induction l with
  | nil => simp [conjsOf, IsQF]
  | cons a as ih =>
      simp only [conjsOf, IsQF]
      rw [ih]
      constructor
      · rintro ⟨h1, h2⟩ f hf
        rcases List.mem_cons.mp hf with rfl | hf'
        · exact h1
        · exact h2 f hf'
      · intro h
        exact ⟨h a (List.mem_cons.mpr (Or.inl rfl)),
               fun f hf' => h f (List.mem_cons.mpr (Or.inr hf'))⟩

/-- 无量词的右结合析取（定理 TH-2 的列表侧） -/
theorem isQF_disjsOf : ∀ l : List Formula, IsQF (disjsOf l) ↔ ∀ f ∈ l, IsQF f := by
  intro l
  induction l with
  | nil => simp [disjsOf, IsQF]
  | cons a as ih =>
      simp only [disjsOf, IsQF]
      rw [ih]
      constructor
      · rintro ⟨h1, h2⟩ f hf
        rcases List.mem_cons.mp hf with rfl | hf'
        · exact h1
        · exact h2 f hf'
      · intro h
        exact ⟨h a (List.mem_cons.mpr (Or.inl rfl)),
               fun f hf' => h f (List.mem_cons.mpr (Or.inr hf'))⟩

/-- 索引元组枚举的成员刻画（规范 §3.6.1）：
    `tuplesOf n k` 恰好是所有「长度 `k` 且每个元素 `< n`」的索引列表。

    证明计划（对 `k` 归纳，并 `generalizing is`）：
    * `k = 0`：`tuplesOf n 0 = [[]]`，故 `is ∈ [[]] ↔ is = []`；
      再用 `List.eq_nil_of_length_eq_zero` 反向转换。
    * `k + 1`：`rw [tuplesOf, tuplesStep, List.mem_bind, List.mem_range, List.mem_map]`
      后，左式化为 `∃ i < n, ∃ is' ∈ tuplesOf n k, is = i :: is'`，
      对 `is'` 用归纳假设即得两方向；反向取 `i := is.head`、`is' := is.tail`。

    该引理是 TH-1 量词分支的**唯一实质性义务**，登记为 `12 §12.6` 的
    `OBL-1`（首个 `lake build` 后的首要补证项）。 -/
theorem mem_tuplesOf {n k : Nat} {is : List Nat} :
    is ∈ tuplesOf n k ↔ is.length = k ∧ ∀ i ∈ is, i < n := by
  sorry

/-- 单射枚举的成员刻画（规范 §3.5.2 的 `Inj`） -/
theorem mem_injectiveTuplesOf {n k : Nat} {is : List Nat} :
    is ∈ injectiveTuplesOf n k ↔ is.length = k ∧ (∀ i ∈ is, i < n) ∧ is.Nodup := by
  unfold injectiveTuplesOf
  rw [List.mem_filter, mem_tuplesOf]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, of_decide_eq_true h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, decide_eq_true h3⟩

/-- 索引族 `tupleFamily` 的成员刻画：把「属于枚举族」等价为规范 §3.5.2
    量词语义中的三条界条件（长度匹配、元素在域内、`distinct` 时无重复）。
    这是定理 TH-1 量词分支的**唯一实质性引理**。 -/
theorem mem_tupleFamily {n k : Nat} {distinct : Bool} {is : List Nat} :
    is ∈ tupleFamily n k distinct ↔
      is.length = k ∧ (∀ i ∈ is, i < n) ∧ (distinct = true → is.Nodup) := by
  unfold tupleFamily
  cases distinct with
  | false => simp [mem_tuplesOf]
  | true => simp [mem_injectiveTuplesOf]

/-! ## 定理 TH-1：Grounding 保持定理 -/

/-- **定理 TH-1（Grounding Preservation，规范 §3.7）**

    设 `hE` 为原子解释器的**重命名等变性**假设：
    规范 §3.6.2 的引理 L1（重命名一致性）要求
    `E ρ (groundAtom ρ a) ↔ E ρ a`——即原子语义对绑定变量与对应展平标量
    给出相同取值。这一假设在三处得到落实：
    (a) Rust 侧 `ground_expr` 与 `scalar_symbol` 的单射命名（`03 §3.2.4`）；
    (b) Lean 侧 `Term.flat` 与 `Term.fieldAccess` 的语义同构；
    (c) `06 §6.2` 的展平声明发射。

    结论：对任意合式公式 `φ` 与环境 `ρ`，
    `⟦ground(φ)⟧ρ = ⟦φ⟧ρ`，即展开变换**保持语义**。 -/
theorem ground_preserves (E : AtomEval)
    (hE : ∀ (ρ : Env) (a : Atom), E ρ (groundAtom ρ a) ↔ E ρ a)
    (M : Model) (ρ : Env) (φ : Formula) :
    eval E M ρ (ground M ρ φ) ↔ eval E M ρ φ := by
  induction φ generalizing ρ with
  | tt => simp [ground, eval]
  | ff => simp [ground, eval]
  | atom a => simpa only [ground, eval] using hE ρ a
  | conj a b iha ihb =>
      simp only [ground, eval]
      exact ⟨fun h => ⟨(iha ρ).mp h.1, (ihb ρ).mp h.2⟩,
             fun h => ⟨(iha ρ).mpr h.1, (ihb ρ).mpr h.2⟩⟩
  | disj a b iha ihb =>
      simp only [ground, eval]
      exact ⟨fun h => h.elim (fun h1 => Or.inl ((iha ρ).mp h1))
                             (fun h2 => Or.inr ((ihb ρ).mp h2)),
             fun h => h.elim (fun h1 => Or.inl ((iha ρ).mpr h1))
                             (fun h2 => Or.inr ((ihb ρ).mpr h2))⟩
  | neg f ih =>
      simp only [ground, eval]
      exact ⟨fun h => (ih ρ).mp h, fun h => (ih ρ).mpr h⟩
  | impl a b iha ihb =>
      simp only [ground, eval]
      exact ⟨fun h h1 => (ihb ρ).mp (h ((iha ρ).mpr h1)),
             fun h h1 => (ihb ρ).mpr (h ((iha ρ).mp h1))⟩
  | biff a b iha ihb =>
      simp only [ground, eval]
      exact ⟨fun h => (iha ρ).symm.trans (h.trans (ihb ρ)),
             fun h => (iha ρ).trans (h.trans (ihb ρ).symm)⟩
  | qall vars dom distinct body ih =>
      simp only [ground]
      rw [eval_conjsOf, forall_mem_map]
      constructor
      · intro h is hlen hinb hnod
        exact (ih (ρ.bindAll dom vars is)).mp
                (h is (mem_tupleFamily.mpr ⟨hlen, hinb, hnod⟩))
      · intro h is his
        obtain ⟨hlen, hinb, hnod⟩ := mem_tupleFamily.mp his
        exact (ih (ρ.bindAll dom vars is)).mpr (h is hlen hinb hnod)
  | qex vars dom distinct body ih =>
      simp only [ground]
      rw [eval_disjsOf, exists_mem_map]
      constructor
      · rintro ⟨is, his, h⟩
        obtain ⟨hlen, hinb, hnod⟩ := mem_tupleFamily.mp his
        exact ⟨is, hlen, hinb, hnod, (ih (ρ.bindAll dom vars is)).mp h⟩
      · rintro ⟨is, hlen, hinb, hnod, h⟩
        exact ⟨is, mem_tupleFamily.mpr ⟨hlen, hinb, hnod⟩,
                (ih (ρ.bindAll dom vars is)).mpr h⟩

/-- **推论 TH-1-C1（解集保持）**：`ground` 逐点保持语义，故其解集与模型集不变。 -/
theorem ground_preserves_iff (E : AtomEval)
    (hE : ∀ (ρ : Env) (a : Atom), E ρ (groundAtom ρ a) ↔ E ρ a)
    (M : Model) (φ : Formula) :
    (∃ ρ, eval E M ρ (ground M ρ φ)) ↔ ∃ ρ, eval E M ρ φ := by
  constructor
  · rintro ⟨ρ, h⟩; exact ⟨ρ, (ground_preserves E hE M ρ φ).mp h⟩
  · rintro ⟨ρ, h⟩; exact ⟨ρ, (ground_preserves E hE M ρ φ).mpr h⟩

/-- **推论 TH-1-C2（反例可唯一还原，规范 §3.7）**

    `Term.flat` 携带 `(Instance, field)` 两元组且为单射，因此任一展平模型中的
    标量符号都可**唯一**逆解析回业务视图 `D[i].f`。 -/
theorem flat_injective {i j : Instance} {f g : String}
    (h : Term.flat i f = Term.flat j g) : i = j ∧ f = g := by
  injection h with h1 h2
  exact ⟨h1, h2⟩

/-! ## 定理 TH-2：量词消除 -/

/-- **定理 TH-2（Quantifier-Freeness，规范 §3.8）**

    `ground` 的输出中**不含 `qall`/`qex` 节点**。证明为对 `φ` 的结构归纳：
    递归子句仅在原位置保留原构造，量词子句被替换为 `conjsOf` / `disjsOf`
    包裹的枚举结果，而 `conjsOf`/`disjsOf` 本身只由 `tt`/`ff`/`conj`/`disj` 构成。

    该定理是规范 §3.8「输出 100% 无量词」断言的**机械化证据**。 -/
theorem ground_isQF (M : Model) (ρ : Env) (φ : Formula) : IsQF (ground M ρ φ) := by
  induction φ generalizing ρ with
  | tt => simp [ground, IsQF]
  | ff => simp [ground, IsQF]
  | atom a => simp [ground, IsQF]
  | conj a b iha ihb => simp only [ground, IsQF]; exact ⟨iha ρ, ihb ρ⟩
  | disj a b iha ihb => simp only [ground, IsQF]; exact ⟨iha ρ, ihb ρ⟩
  | neg f ih => simp only [ground, IsQF]; exact ih ρ
  | impl a b iha ihb => simp only [ground, IsQF]; exact ⟨iha ρ, ihb ρ⟩
  | biff a b iha ihb => simp only [ground, IsQF]; exact ⟨iha ρ, ihb ρ⟩
  | qall vars dom distinct body ih =>
      simp only [ground]
      refine (isQF_conjsOf _).mpr ?_
      rw [forall_mem_map]
      intro is _
      exact ih (ρ.bindAll dom vars is)
  | qex vars dom distinct body ih =>
      simp only [ground]
      refine (isQF_disjsOf _).mpr ?_
      rw [forall_mem_map]
      intro is _
      exact ih (ρ.bindAll dom vars is)

end Policylang
