import SparseStack.Prob.Resample
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Powerset

/-!
# Paley–Zygmund, weighted Bernoulli lower tail, subset bound (contracts 3, 5, 6)

Paper, Section 3 (lines 161–196) and the proof of `lem:smallball` (lines 271–291).

* `paley_zygmund`: `(1-θ)² (E V)² ≤ P{V ≥ θ E V} E V²` (Cauchy–Schwarz on `E[V 1_{V ≥ θ E V}]`).
* `weighted_bernoulli_lower_tail`: for events `E j` depending on disjoint blocks with
  `P(E j) ≥ π`, `P{∑ v_j 1_{E_j} < κ' ∑ v_j} ≤ exp((κ'/2 - 25π/64) ∑ v_j / vmax)`; proof:
  `1 - e^{-u} ≥ (25/32) u` on `[0, 1/2]` (convexity of `exp` and `e^{1/2} > 64/39`), block
  factorization of `E exp(-∑ v_j 1_{E_j} / (2 vmax))`, exponential Markov.
* `subset_bound`: for events on disjoint blocks with `P(E j) ≤ π ≤ 1`, the probability that at
  least `u` of them occur is at most `2^m π^u`; proof: union over the subsets `T` with
  `u ≤ |T|` and `P(⋂_{j ∈ T} E j) = ∏_{j ∈ T} P(E j) ≤ π^|T| ≤ π^u`.
-/

open scoped BigOperators

namespace SparseStack

open SparseFock

/-! ## Paley–Zygmund (contract 3) -/

/-- **Paley–Zygmund inequality** (paper display `eq:fourth-smallball` is the case `θ = 1/2`). -/
theorem paley_zygmund {α : Type*} [Fintype α] (μ : FiniteLaw α) (V : α → ℝ)
    (hV : ∀ x, 0 ≤ V x) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * μ.expect V ^ 2 ≤
      μ.prob {x | θ * μ.expect V ≤ V x} * μ.expect (fun x => V x ^ 2) := by
  set m := μ.expect V with hm
  set A : Set α := {x | θ * m ≤ V x} with hA
  have hm0 : 0 ≤ m := μ.expect_nonneg hV
  -- `E V ≤ θ E V + E[V 1_A]`
  have h1 : m ≤ θ * m + μ.expect (fun x => V x * FiniteLaw.indicator A x) := by
    have hpt : ∀ x, V x ≤ θ * m + V x * FiniteLaw.indicator A x := by
      intro x
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx]
        nlinarith
      · rw [indicator_of_notMem hx]
        have hx' : ¬ θ * m ≤ V x := hx
        linarith
    calc m = μ.expect V := rfl
      _ ≤ μ.expect (fun x => θ * m + V x * FiniteLaw.indicator A x) := μ.expect_mono hpt
      _ = θ * m + μ.expect (fun x => V x * FiniteLaw.indicator A x) := by
        rw [FiniteLaw.expect_add, FiniteLaw.expect_const]
  -- Cauchy–Schwarz: `E[V 1_A]² ≤ P(A) E[V²]`
  have h2 : μ.expect (fun x => V x * FiniteLaw.indicator A x) ^ 2 ≤
      μ.prob A * μ.expect (fun x => V x ^ 2) := by
    unfold FiniteLaw.prob FiniteLaw.expect
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro x _
      exact mul_nonneg (μ.weight_nonneg x) (indicator_nonneg A x)
    · intro x _
      exact mul_nonneg (μ.weight_nonneg x) (sq_nonneg _)
    · intro x _
      have hsq := indicator_sq A x
      have heq : (μ.weight x * (V x * FiniteLaw.indicator A x)) ^ 2 =
          μ.weight x * FiniteLaw.indicator A x * (μ.weight x * V x ^ 2) := by
        calc (μ.weight x * (V x * FiniteLaw.indicator A x)) ^ 2
            = μ.weight x ^ 2 * V x ^ 2 * FiniteLaw.indicator A x ^ 2 := by ring
          _ = μ.weight x ^ 2 * V x ^ 2 * FiniteLaw.indicator A x := by rw [hsq]
          _ = μ.weight x * FiniteLaw.indicator A x * (μ.weight x * V x ^ 2) := by ring
      exact heq.le
  have h3 : 0 ≤ (1 - θ) * m := mul_nonneg (by linarith) hm0
  have h4 : (1 - θ) * m ≤ μ.expect (fun x => V x * FiniteLaw.indicator A x) := by linarith
  calc (1 - θ) ^ 2 * m ^ 2 = ((1 - θ) * m) ^ 2 := by ring
    _ ≤ μ.expect (fun x => V x * FiniteLaw.indicator A x) ^ 2 := pow_le_pow_left₀ h3 h4 2
    _ ≤ μ.prob A * μ.expect (fun x => V x ^ 2) := h2

/-! ## Weighted Bernoulli lower tail (contract 5) -/

/-- `e^{-1/2} ≤ 39/64`, i.e. `e^{1/2} ≥ 64/39` (from `e > 2.7182818283`). -/
theorem exp_neg_half_le : Real.exp (-(1 / 2)) ≤ 39 / 64 := by
  have he : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have h1 : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h2 : Real.exp (-(1 / 2)) ^ 2 = Real.exp (-1) := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hpos1 : 0 < Real.exp (-1) := Real.exp_pos _
  have hpos2 : 0 < Real.exp (-(1 / 2)) := Real.exp_pos _
  have h3 : Real.exp (-1) < 1521 / 4096 := by nlinarith
  nlinarith

/-- `1 - e^{-u} ≥ (25/32) u` for `0 ≤ u ≤ 1/2` (paper line 274). -/
theorem one_sub_exp_neg_ge {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    25 / 32 * u ≤ 1 - Real.exp (-u) := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-(1 / 2) : ℝ))
    (show (0 : ℝ) ≤ 1 - 2 * u by linarith) (show (0 : ℝ) ≤ 2 * u by linarith) (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  have h : 2 * u * -(1 / 2) = -u := by ring
  rw [h] at hconv
  have h5 := exp_neg_half_le
  nlinarith

/-- **Weighted Bernoulli lower tail** (paper lines 271–291) for events determined by pairwise
disjoint blocks of coordinates of an independent product. -/
theorem weighted_bernoulli_lower_tail {ι α κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [Fintype κ] (μ : ι → FiniteLaw α) (S : κ → Finset ι)
    (hS : Pairwise (fun j k => Disjoint (S j) (S k)))
    (E : κ → Set (ι → α)) (hE : ∀ j x y, (∀ i ∈ S j, x i = y i) → (x ∈ E j ↔ y ∈ E j))
    {π : ℝ} (hπ0 : 0 ≤ π) (hπ : ∀ j, π ≤ (FiniteLaw.independentProduct μ).prob (E j))
    (v : κ → ℝ) {vmax : ℝ} (hv0 : ∀ j, 0 ≤ v j) (hvmax : ∀ j, v j ≤ vmax) (hvmax0 : 0 < vmax)
    {κ' : ℝ} (hκ' : 0 ≤ κ') :
    (FiniteLaw.independentProduct μ).prob
        {x | ∑ j, v j * FiniteLaw.indicator (E j) x < κ' * ∑ j, v j} ≤
      Real.exp ((κ' / 2 - 25 / 64 * π) * (∑ j, v j) / vmax) := by
  -- The hypothesis `0 ≤ κ'` (part of the contract) is not needed: exponential Markov works for
  -- every threshold.
  have _ : 0 ≤ κ' := hκ'
  set P := FiniteLaw.independentProduct μ with hP
  set lam := 1 / (2 * vmax) with hlam
  have hlam0 : 0 < lam := by positivity
  have hdep : ∀ j x y, (∀ i ∈ S j, x i = y i) →
      FiniteLaw.indicator (E j) x = FiniteLaw.indicator (E j) y := by
    intro j x y hxy
    have hiff := hE j x y hxy
    by_cases hx : x ∈ E j
    · rw [indicator_of_mem hx, indicator_of_mem (hiff.mp hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun hy => hx (hiff.mpr hy))]
  -- factorization of the moment generating function over the blocks
  have hfact : P.expect (fun x => Real.exp (-lam * ∑ j, v j * FiniteLaw.indicator (E j) x)) =
      ∏ j, P.expect (fun x => Real.exp (-lam * (v j * FiniteLaw.indicator (E j) x))) := by
    rw [← expect_prod_disjoint_blocks μ S hS
      (fun j x => Real.exp (-lam * (v j * FiniteLaw.indicator (E j) x)))]
    · apply P.expect_congr
      intro x
      rw [Finset.mul_sum, Real.exp_sum]
    · intro j x y hxy
      simp only [hdep j x y hxy]
  -- each factor: `E exp(-λ v_j 1_{E_j}) = 1 - (1 - e^{-λ v_j}) P(E_j) ≤ exp(-(25/64) π v_j/vmax)`
  have hfactor : ∀ j, P.expect (fun x => Real.exp (-lam * (v j * FiniteLaw.indicator (E j) x))) ≤
      Real.exp (-(25 / 64 * π) * v j / vmax) := by
    intro j
    have hu0 : 0 ≤ lam * v j := mul_nonneg hlam0.le (hv0 j)
    have hu1 : lam * v j ≤ 1 / 2 := by
      rw [hlam, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      linarith [hvmax j]
    have hpt : ∀ x, Real.exp (-lam * (v j * FiniteLaw.indicator (E j) x)) =
        1 - (1 - Real.exp (-(lam * v j))) * FiniteLaw.indicator (E j) x := by
      intro x
      by_cases hx : x ∈ E j
      · rw [indicator_of_mem hx, show -lam * (v j * 1) = -(lam * v j) by ring]
        ring
      · rw [indicator_of_notMem hx]
        simp
    rw [P.expect_congr hpt, FiniteLaw.expect_sub, FiniteLaw.expect_one, FiniteLaw.expect_smul]
    have hprob : P.expect (FiniteLaw.indicator (E j)) = P.prob (E j) := rfl
    rw [hprob]
    have hkey := one_sub_exp_neg_ge hu0 hu1
    have h2 : 0 ≤ 1 - Real.exp (-(lam * v j)) := by linarith
    have h1 : 25 / 32 * (lam * v j) * π ≤ (1 - Real.exp (-(lam * v j))) * P.prob (E j) :=
      calc 25 / 32 * (lam * v j) * π ≤ (1 - Real.exp (-(lam * v j))) * π :=
            mul_le_mul_of_nonneg_right hkey hπ0
        _ ≤ (1 - Real.exp (-(lam * v j))) * P.prob (E j) := mul_le_mul_of_nonneg_left (hπ j) h2
    have h3 : 1 - 25 / 32 * (lam * v j) * π ≤ Real.exp (-(25 / 32 * (lam * v j) * π)) := by
      linarith [Real.add_one_le_exp (-(25 / 32 * (lam * v j) * π))]
    have h4 : -(25 / 32 * (lam * v j) * π) = -(25 / 64 * π) * v j / vmax := by
      rw [hlam]
      field_simp
      ring
    rw [← h4]
    linarith
  -- exponential Markov
  have hsub : {x | ∑ j, v j * FiniteLaw.indicator (E j) x < κ' * ∑ j, v j} ⊆
      {x | Real.exp (-lam * (κ' * ∑ j, v j)) ≤
        Real.exp (-lam * ∑ j, v j * FiniteLaw.indicator (E j) x)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    apply Real.exp_le_exp.mpr
    nlinarith
  calc P.prob {x | ∑ j, v j * FiniteLaw.indicator (E j) x < κ' * ∑ j, v j}
      ≤ P.prob {x | Real.exp (-lam * (κ' * ∑ j, v j)) ≤
          Real.exp (-lam * ∑ j, v j * FiniteLaw.indicator (E j) x)} :=
        prob_le_of_subset P hsub
    _ ≤ P.expect (fun x => Real.exp (-lam * ∑ j, v j * FiniteLaw.indicator (E j) x)) /
          Real.exp (-lam * (κ' * ∑ j, v j)) :=
        P.markov (fun x => (Real.exp_pos _).le) (Real.exp_pos _)
    _ = (∏ j, P.expect (fun x => Real.exp (-lam * (v j * FiniteLaw.indicator (E j) x)))) /
          Real.exp (-lam * (κ' * ∑ j, v j)) := by
        rw [hfact]
    _ ≤ (∏ j, Real.exp (-(25 / 64 * π) * v j / vmax)) /
          Real.exp (-lam * (κ' * ∑ j, v j)) := by
        apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
        apply Finset.prod_le_prod
        · intro j _
          exact P.expect_nonneg (fun x => (Real.exp_pos _).le)
        · intro j _
          exact hfactor j
    _ = Real.exp ((κ' / 2 - 25 / 64 * π) * (∑ j, v j) / vmax) := by
        rw [← Real.exp_sum, ← Real.exp_sub, ← Finset.sum_div, ← Finset.mul_sum]
        congr 1
        rw [hlam]
        field_simp
        ring

/-! ## Subset bound (contract 6) -/

open Classical in
/-- **Subset bound** (paper display `eq:subset-bound`): for events determined by pairwise
disjoint blocks, each of probability at most `π ≤ 1`, the probability that at least `u ≥ 0` of
them occur is at most `2^m π^u` (`π^u` is `Real.rpow`, `m` the number of events). -/
theorem subset_bound {ι α κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype κ]
    (μ : ι → FiniteLaw α) (S : κ → Finset ι)
    (hS : Pairwise (fun j k => Disjoint (S j) (S k)))
    (E : κ → Set (ι → α)) (hE : ∀ j x y, (∀ i ∈ S j, x i = y i) → (x ∈ E j ↔ y ∈ E j))
    {π : ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hπ : ∀ j, (FiniteLaw.independentProduct μ).prob (E j) ≤ π) {u : ℝ} (hu : 0 ≤ u) :
    (FiniteLaw.independentProduct μ).prob
        {x | u ≤ ((Finset.univ.filter (fun j => x ∈ E j)).card : ℝ)} ≤
      2 ^ Fintype.card κ * π ^ u := by
  set P := FiniteLaw.independentProduct μ with hP
  have hdep : ∀ j x y, (∀ i ∈ S j, x i = y i) →
      FiniteLaw.indicator (E j) x = FiniteLaw.indicator (E j) y := by
    intro j x y hxy
    have hiff := hE j x y hxy
    by_cases hx : x ∈ E j
    · rw [indicator_of_mem hx, indicator_of_mem (hiff.mp hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun hy => hx (hiff.mpr hy))]
  -- the subsets of size at least `u`
  set 𝒯 : Finset (Finset κ) := Finset.univ.filter (fun T => u ≤ (T.card : ℝ)) with h𝒯
  have hprod_nonneg : ∀ (T : Finset κ) (x : ι → α), 0 ≤ ∏ j ∈ T, FiniteLaw.indicator (E j) x :=
    fun T x => Finset.prod_nonneg (fun j _ => indicator_nonneg _ _)
  -- pointwise domination of the indicator of the event
  have hpt : ∀ x, FiniteLaw.indicator
      {x | u ≤ ((Finset.univ.filter (fun j => x ∈ E j)).card : ℝ)} x ≤
      ∑ T ∈ 𝒯, ∏ j ∈ T, FiniteLaw.indicator (E j) x := by
    intro x
    by_cases hx : u ≤ ((Finset.univ.filter (fun j => x ∈ E j)).card : ℝ)
    · rw [indicator_of_mem (show x ∈ {x | u ≤ ((Finset.univ.filter
          (fun j => x ∈ E j)).card : ℝ)} from hx)]
      have hT₀ : Finset.univ.filter (fun j => x ∈ E j) ∈ 𝒯 := by
        rw [h𝒯, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hx⟩
      have hone : ∏ j ∈ Finset.univ.filter (fun j => x ∈ E j), FiniteLaw.indicator (E j) x = 1 := by
        apply Finset.prod_eq_one
        intro j hj
        rw [Finset.mem_filter] at hj
        exact indicator_of_mem hj.2
      rw [← hone]
      exact Finset.single_le_sum (fun T _ => hprod_nonneg T x) hT₀
    · rw [indicator_of_notMem (show x ∉ {x | u ≤ ((Finset.univ.filter
          (fun j => x ∈ E j)).card : ℝ)} from hx)]
      exact Finset.sum_nonneg (fun T _ => hprod_nonneg T x)
  -- each intersection has probability at most `π^u`
  have hT : ∀ T ∈ 𝒯, P.expect (fun x => ∏ j ∈ T, FiniteLaw.indicator (E j) x) ≤ π ^ u := by
    intro T hT
    rw [h𝒯, Finset.mem_filter] at hT
    rw [expect_prod_disjoint_blocks_finset μ S hS (fun j => FiniteLaw.indicator (E j)) hdep T]
    calc ∏ j ∈ T, P.expect (FiniteLaw.indicator (E j)) ≤ ∏ _j ∈ T, π := by
          apply Finset.prod_le_prod
          · intro j _
            exact P.prob_nonneg (E j)
          · intro j _
            exact hπ j
      _ = π ^ T.card := Finset.prod_const π
      _ = π ^ (T.card : ℝ) := (Real.rpow_natCast π T.card).symm
      _ ≤ π ^ u := Real.rpow_le_rpow_of_exponent_ge' hπ0 hπ1 hu hT.2
  have hcard : (𝒯.card : ℝ) ≤ 2 ^ Fintype.card κ := by
    have h1 : 𝒯.card ≤ 2 ^ Fintype.card κ := by
      calc 𝒯.card ≤ (Finset.univ : Finset (Finset κ)).card := Finset.card_filter_le _ _
        _ = 2 ^ Fintype.card κ := by rw [Finset.card_univ, Fintype.card_finset]
    exact_mod_cast h1
  calc P.prob {x | u ≤ ((Finset.univ.filter (fun j => x ∈ E j)).card : ℝ)}
      ≤ P.expect (fun x => ∑ T ∈ 𝒯, ∏ j ∈ T, FiniteLaw.indicator (E j) x) :=
        P.expect_mono hpt
    _ = ∑ T ∈ 𝒯, P.expect (fun x => ∏ j ∈ T, FiniteLaw.indicator (E j) x) :=
        expect_sum P 𝒯 _
    _ ≤ ∑ _T ∈ 𝒯, π ^ u := Finset.sum_le_sum hT
    _ = (𝒯.card : ℝ) * π ^ u := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ Fintype.card κ * π ^ u :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hπ0 u)

end SparseStack
