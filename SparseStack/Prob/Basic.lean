import SparseFockFormal.FiniteProbability

/-!
# Finite probability toolkit: basic helpers

Helpers on top of Heidary's finite laws `SparseFock.FiniteLaw`:

* indicator lemmas, `prob_congr`, `prob_le_of_subset`, union bounds (`prob_union_le`,
  `prob_union_le_sum`, `prob_iUnion_le_sum`) and complement helpers (contract 7);
* reindexing of independent products along an equivalence and the sum split
  `expect_independentProduct_sum_split`, with its `prob` and general-equivalence versions
  (contract 8);
* the uniform law `uniformLaw`, with `uniformLaw_prob` and `independentProduct_uniformLaw`
  (contract 9), and binary products `prodLaw` (Heidary's `FiniteProductLaw` module is not
  built in `vendor/`, so it is not imported here).
-/

open scoped BigOperators

namespace SparseStack

open SparseFock

noncomputable section

/-! ## Indicators, expectations, probabilities, union bounds (contract 7) -/

section Indicator

variable {α : Type*}

theorem indicator_of_mem {s : Set α} {x : α} (h : x ∈ s) : FiniteLaw.indicator s x = 1 := by
  simp [FiniteLaw.indicator, h]

theorem indicator_of_notMem {s : Set α} {x : α} (h : x ∉ s) :
    FiniteLaw.indicator s x = 0 := by
  simp [FiniteLaw.indicator, h]

theorem indicator_nonneg (s : Set α) (x : α) : 0 ≤ FiniteLaw.indicator s x := by
  by_cases h : x ∈ s
  · rw [indicator_of_mem h]
    norm_num
  · rw [indicator_of_notMem h]

theorem indicator_le_one (s : Set α) (x : α) : FiniteLaw.indicator s x ≤ 1 := by
  by_cases h : x ∈ s
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h]
    norm_num

theorem indicator_sq (s : Set α) (x : α) :
    FiniteLaw.indicator s x ^ 2 = FiniteLaw.indicator s x := by
  by_cases h : x ∈ s
  · rw [indicator_of_mem h]
    norm_num
  · rw [indicator_of_notMem h]
    norm_num

end Indicator

section Basic

variable {α : Type*} [Fintype α]

/-- Two finite laws with the same weights are equal. -/
theorem finiteLaw_ext {μ ν : FiniteLaw α} (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ
  cases ν
  congr
  funext x
  exact h x

/-- A finite law lives on a nonempty type. -/
theorem finiteLaw_nonempty (μ : FiniteLaw α) : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 := μ.sum_weight
  rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
  exact zero_ne_one h1

theorem expect_mul_const (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.expect (fun x => f x * c) = μ.expect f * c := by
  rw [mul_comm, ← FiniteLaw.expect_smul]
  apply μ.expect_congr
  intro x
  ring

theorem expect_sum {ι : Type*} (μ : FiniteLaw α) (s : Finset ι) (f : ι → α → ℝ) :
    μ.expect (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, μ.expect (f i) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem prob_congr (μ : FiniteLaw α) {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) :
    μ.prob s = μ.prob t := by
  rw [Set.ext h]

theorem prob_le_of_subset (μ : FiniteLaw α) {s t : Set α} (h : s ⊆ t) :
    μ.prob s ≤ μ.prob t :=
  μ.prob_mono h

theorem prob_union_le (μ : FiniteLaw α) (s t : Set α) :
    μ.prob (s ∪ t) ≤ μ.prob s + μ.prob t := by
  unfold FiniteLaw.prob
  rw [← FiniteLaw.expect_add]
  apply μ.expect_mono
  intro x
  by_cases hs : x ∈ s
  · have hst : x ∈ s ∪ t := Or.inl hs
    rw [indicator_of_mem hst, indicator_of_mem hs]
    linarith [indicator_nonneg t x]
  · by_cases ht : x ∈ t
    · have hst : x ∈ s ∪ t := Or.inr ht
      rw [indicator_of_mem hst, indicator_of_mem ht]
      linarith [indicator_nonneg s x]
    · have hst : x ∉ s ∪ t := fun h => h.elim hs ht
      rw [indicator_of_notMem hst, indicator_of_notMem hs, indicator_of_notMem ht]
      norm_num

/-- Finite union bound over a `Finset` of indices. -/
theorem prob_union_le_sum {ι : Type*} (μ : FiniteLaw α) (s : Finset ι) (E : ι → Set α) :
    μ.prob (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, μ.prob (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (prob_union_le μ _ _).trans (by linarith)

/-- Finite union bound over a `Fintype` of indices. -/
theorem prob_iUnion_le_sum {ι : Type*} [Fintype ι] (μ : FiniteLaw α) (E : ι → Set α) :
    μ.prob (⋃ i, E i) ≤ ∑ i, μ.prob (E i) := by
  have h := prob_union_le_sum μ Finset.univ E
  simpa using h

/-- Complement form: `P(s) = 1 - P(sᶜ)`. (`FiniteLaw.prob_compl` is Heidary's `P(sᶜ) = 1 - P(s)`.) -/
theorem prob_eq_one_sub_prob_compl (μ : FiniteLaw α) (s : Set α) :
    μ.prob s = 1 - μ.prob sᶜ := by
  rw [μ.prob_compl]
  ring

/-- If the failure event `sᶜ` has probability at most `δ`, then `P(s) ≥ 1 - δ`. -/
theorem one_sub_le_prob_of_prob_compl_le (μ : FiniteLaw α) {s : Set α} {δ : ℝ}
    (h : μ.prob sᶜ ≤ δ) : 1 - δ ≤ μ.prob s := by
  rw [prob_eq_one_sub_prob_compl μ s]
  linarith

/-- Combining failure events: if every outcome avoiding all the bad events `bad i` (`i ∈ s`)
is good, then `P(good) ≥ 1 - ∑ P(bad i)`. -/
theorem one_sub_sum_le_prob {ι : Type*} (μ : FiniteLaw α) (good : Set α) (s : Finset ι)
    (bad : ι → Set α) (h : ∀ x, (∀ i ∈ s, x ∉ bad i) → x ∈ good) :
    1 - ∑ i ∈ s, μ.prob (bad i) ≤ μ.prob good := by
  have hsub : goodᶜ ⊆ ⋃ i ∈ s, bad i := by
    intro x hx
    by_contra hcon
    simp only [Set.mem_iUnion, not_exists] at hcon
    exact hx (h x (fun i hi => hcon i hi))
  have h1 := (prob_le_of_subset μ hsub).trans (prob_union_le_sum μ s bad)
  apply one_sub_le_prob_of_prob_compl_le
  exact h1

end Basic

/-! ## Reindexing and splitting independent products (contract 8) -/

section Split

/-- Reindex an independent product along an equivalence `e : ι ≃ ι'`. -/
theorem expect_independentProduct_equiv {ι ι' α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] [Fintype α] (e : ι ≃ ι') (μ : ι' → FiniteLaw α)
    (F : (ι' → α) → ℝ) :
    (FiniteLaw.independentProduct μ).expect F =
      (FiniteLaw.independentProduct (fun i => μ (e i))).expect
        (fun x => F (fun i' => x (e.symm i'))) := by
  simp only [FiniteLaw.expect, FiniteLaw.independentProduct_weight]
  symm
  refine Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl α)) _ _ ?_
  intro x
  have hprod : (∏ i, (μ (e i)).weight (x i)) = ∏ i', (μ i').weight (x (e.symm i')) := by
    rw [← Equiv.prod_comp e (fun i' => (μ i').weight (x (e.symm i')))]
    simp only [Equiv.symm_apply_apply]
  rw [hprod]
  rfl

/-- Fubini for an independent product indexed by a sum type. -/
theorem expect_independentProduct_sum_split {ι₁ ι₂ α : Type*} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂] [Fintype α] (μ : ι₁ ⊕ ι₂ → FiniteLaw α)
    (F : (ι₁ ⊕ ι₂ → α) → ℝ) :
    (FiniteLaw.independentProduct μ).expect F =
      (FiniteLaw.independentProduct (fun i => μ (Sum.inl i))).expect (fun x₁ =>
        (FiniteLaw.independentProduct (fun i => μ (Sum.inr i))).expect (fun x₂ =>
          F (Sum.elim x₁ x₂))) := by
  simp only [FiniteLaw.expect, FiniteLaw.independentProduct_weight]
  rw [← (Equiv.sumArrowEquivProdArrow ι₁ ι₂ α).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x₂ _
  have hsymm : (Equiv.sumArrowEquivProdArrow ι₁ ι₂ α).symm (x₁, x₂) = Sum.elim x₁ x₂ := rfl
  rw [hsymm, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

/-- Event version of `expect_independentProduct_sum_split`. -/
theorem prob_independentProduct_sum_split {ι₁ ι₂ α : Type*} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂] [Fintype α] (μ : ι₁ ⊕ ι₂ → FiniteLaw α)
    (E : Set (ι₁ ⊕ ι₂ → α)) :
    (FiniteLaw.independentProduct μ).prob E =
      (FiniteLaw.independentProduct (fun i => μ (Sum.inl i))).expect (fun x₁ =>
        (FiniteLaw.independentProduct (fun i => μ (Sum.inr i))).prob
          {x₂ | Sum.elim x₁ x₂ ∈ E}) := by
  rw [FiniteLaw.prob, expect_independentProduct_sum_split]
  rfl

/-- Fubini for an independent product along a general splitting `e : ι ≃ ι₁ ⊕ ι₂`
(e.g. `(Equiv.sumCompl p).symm`). -/
theorem expect_independentProduct_equiv_sum_split {ι ι₁ ι₂ α : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [Fintype α]
    (e : ι ≃ ι₁ ⊕ ι₂) (μ : ι → FiniteLaw α) (F : (ι → α) → ℝ) :
    (FiniteLaw.independentProduct μ).expect F =
      (FiniteLaw.independentProduct (fun i => μ (e.symm (Sum.inl i)))).expect (fun x₁ =>
        (FiniteLaw.independentProduct (fun i => μ (e.symm (Sum.inr i)))).expect (fun x₂ =>
          F (fun i => Sum.elim x₁ x₂ (e i)))) := by
  rw [expect_independentProduct_equiv e.symm μ F,
    expect_independentProduct_sum_split (fun o => μ (e.symm o))]
  simp only [Equiv.symm_symm]

/-- Event version of `expect_independentProduct_equiv_sum_split`. -/
theorem prob_independentProduct_equiv_sum_split {ι ι₁ ι₂ α : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [Fintype α]
    (e : ι ≃ ι₁ ⊕ ι₂) (μ : ι → FiniteLaw α) (E : Set (ι → α)) :
    (FiniteLaw.independentProduct μ).prob E =
      (FiniteLaw.independentProduct (fun i => μ (e.symm (Sum.inl i)))).expect (fun x₁ =>
        (FiniteLaw.independentProduct (fun i => μ (e.symm (Sum.inr i)))).prob
          {x₂ | (fun i => Sum.elim x₁ x₂ (e i)) ∈ E}) := by
  rw [FiniteLaw.prob, expect_independentProduct_equiv_sum_split e]
  rfl

end Split

/-! ## The uniform law (contract 9) -/

section Uniform

/-- The uniform law on a nonempty finite type: every outcome has weight `1 / card α`. -/
def uniformLaw (α : Type*) [Fintype α] [Nonempty α] : FiniteLaw α where
  weight _ := 1 / (Fintype.card α : ℝ)
  weight_nonneg _ := by positivity
  sum_weight := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

theorem uniformLaw_weight (α : Type*) [Fintype α] [Nonempty α] (x : α) :
    (uniformLaw α).weight x = 1 / (Fintype.card α : ℝ) := rfl

theorem uniformLaw_expect (α : Type*) [Fintype α] [Nonempty α] (f : α → ℝ) :
    (uniformLaw α).expect f = (∑ x, f x) / (Fintype.card α : ℝ) := by
  simp only [FiniteLaw.expect, uniformLaw_weight, ← Finset.mul_sum]
  ring

theorem uniformLaw_prob (α : Type*) [Fintype α] [Nonempty α] (E : α → Prop) :
    (uniformLaw α).prob {x | E x} = (Nat.card {x // E x} : ℝ) / (Fintype.card α : ℝ) := by
  classical
  rw [FiniteLaw.prob, uniformLaw_expect]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : ∀ x, FiniteLaw.indicator {x | E x} x = if E x then (1 : ℝ) else 0 := by
    intro x
    by_cases hx : E x
    · rw [indicator_of_mem (by exact hx), if_pos hx]
    · rw [indicator_of_notMem (by exact hx), if_neg hx]
  simp only [h]
  rw [Finset.sum_boole]

/-- The independent product of uniform laws is the uniform law on the function type. -/
theorem independentProduct_uniformLaw (ι α : Type*) [Fintype ι] [DecidableEq ι] [Fintype α]
    [Nonempty α] :
    FiniteLaw.independentProduct (fun _ : ι => uniformLaw α) = uniformLaw (ι → α) := by
  apply finiteLaw_ext
  intro x
  rw [FiniteLaw.independentProduct_weight, uniformLaw_weight]
  simp only [uniformLaw_weight, Finset.prod_const, Finset.card_univ, Fintype.card_pi]
  push_cast
  rw [one_div_pow]

end Uniform

/-! ## Binary products of laws -/

section Pair

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The independent product of two finite laws on (possibly different) finite types. -/
def prodLaw (μ : FiniteLaw α) (ν : FiniteLaw β) : FiniteLaw (α × β) where
  weight x := μ.weight x.1 * ν.weight x.2
  weight_nonneg x := mul_nonneg (μ.weight_nonneg x.1) (ν.weight_nonneg x.2)
  sum_weight := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [ν.sum_weight]
    simpa using μ.sum_weight

theorem prodLaw_weight (μ : FiniteLaw α) (ν : FiniteLaw β) (x : α × β) :
    (prodLaw μ ν).weight x = μ.weight x.1 * ν.weight x.2 := rfl

/-- Fubini for `prodLaw`. -/
theorem expect_prodLaw (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α × β → ℝ) :
    (prodLaw μ ν).expect f = μ.expect (fun a => ν.expect (fun b => f (a, b))) := by
  rw [FiniteLaw.expect, FiniteLaw.expect, Fintype.sum_prod_type]
  simp only [prodLaw_weight]
  simp_rw [FiniteLaw.expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Event version of `expect_prodLaw`. -/
theorem prob_prodLaw (μ : FiniteLaw α) (ν : FiniteLaw β) (E : Set (α × β)) :
    (prodLaw μ ν).prob E = μ.expect (fun a => ν.prob {b | (a, b) ∈ E}) := by
  rw [FiniteLaw.prob, expect_prodLaw]
  rfl

end Pair

/-- The product of two uniform laws is the uniform law on the product type. -/
theorem prodLaw_uniformLaw (α β : Type*) [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    prodLaw (uniformLaw α) (uniformLaw β) = uniformLaw (α × β) := by
  apply finiteLaw_ext
  intro x
  rw [prodLaw_weight, uniformLaw_weight, uniformLaw_weight, uniformLaw_weight,
    Fintype.card_prod]
  push_cast
  ring

/-- The uniform law is invariant under every bijection. -/
theorem uniformLaw_expect_comp_equiv (α : Type*) [Fintype α] [Nonempty α] (e : α ≃ α)
    (F : α → ℝ) : (uniformLaw α).expect (fun x => F (e x)) = (uniformLaw α).expect F := by
  rw [uniformLaw_expect, uniformLaw_expect, Equiv.sum_comp e F]

/-- Transport of the uniform law along an equivalence of finite types (e.g. `Equiv.curry`, to
pass between `ι × κ → α` and `ι → κ → α`). -/
theorem uniformLaw_expect_equiv {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (F : β → ℝ) :
    (uniformLaw α).expect (fun x => F (e x)) = (uniformLaw β).expect F := by
  rw [uniformLaw_expect, uniformLaw_expect, Equiv.sum_comp e F, Fintype.card_congr e]

/-- Event version of `uniformLaw_expect_equiv`. -/
theorem uniformLaw_prob_equiv {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (E : Set β) :
    (uniformLaw α).prob {x | e x ∈ E} = (uniformLaw β).prob E :=
  uniformLaw_expect_equiv e (FiniteLaw.indicator E)

/-- Resampling identity for the uniform law along any bijection `e` of pairs: if `x, y` are
independent and uniform, then `(e (x, y)).1` is uniform. (E.g. `e` swapping some coordinates
of `x` and `y`, which gives conditioning on those coordinates.) -/
theorem uniformLaw_expect_expect_equiv (α : Type*) [Fintype α] [Nonempty α]
    (e : α × α ≃ α × α) (F : α → ℝ) :
    (uniformLaw α).expect (fun x => (uniformLaw α).expect (fun y => F (e (x, y)).1)) =
      (uniformLaw α).expect F := by
  have h1 : ∀ G : α × α → ℝ,
      (uniformLaw α).expect (fun x => (uniformLaw α).expect (fun y => G (x, y))) =
        (uniformLaw (α × α)).expect G := by
    intro G
    rw [← prodLaw_uniformLaw, expect_prodLaw]
  rw [h1 (fun p => F (e p).1), uniformLaw_expect_comp_equiv (α × α) e (fun p => F p.1),
    ← h1 (fun p => F p.1)]
  simp only [FiniteLaw.expect_const]

end

end SparseStack
