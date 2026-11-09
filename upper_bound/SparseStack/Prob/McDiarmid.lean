import SparseStack.Prob.Hoeffding
import SparseStack.Prob.Resample

/-!
# McDiarmid's bounded-differences inequality (contract 2)

Paper, Section 3, display (`eq:bounded-differences`): if `f` is a function of independent
variables and changing variable `i` changes `f` by at most `c_i`, then
`P{f - E f ≥ t} ≤ exp(-2t² / ∑ c_i²)`.

Proof plan (Doob martingale): for a set `s` of exposed coordinates let
`F_s = resampleAvg μ sᶜ F` (average out the unexposed coordinates). Exposing one more
coordinate `a`, the increment `F_{s ∪ {a}} - F_s` has conditional range at most `c a`, so by
Hoeffding's lemma `E exp(t (F_{s ∪ {a}} - E F)) ≤ exp(t² c_a² / 8) E exp(t (F_s - E F))`
(`mcdiarmid_step`). Induction over `s` gives `E exp(t (F - E F)) ≤ exp(t² ∑ c_i² / 8)`
(`mcdiarmid_mgf`); exponential Markov with `t = 4 t₀ / ∑ c_i²` finishes.
-/

open scoped BigOperators

namespace SparseStack

open SparseFock

section McDiarmid

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- One step of the Doob martingale: exposing the coordinate `a` costs a factor
`exp(t² c_a² / 8)` in the moment generating function. -/
theorem mcdiarmid_step (μ : ι → FiniteLaw α) (F : (ι → α) → ℝ) (c : ι → ℝ)
    (hF : ∀ x i a, |F (Function.update x i a) - F x| ≤ c i)
    (s : Finset ι) (a : ι) (ha : a ∉ s) (m t : ℝ) :
    (FiniteLaw.independentProduct μ).expect
        (fun x => Real.exp (t * (resampleAvg μ (insert a s)ᶜ F x - m))) ≤
      Real.exp (t ^ 2 * c a ^ 2 / 8) *
        (FiniteLaw.independentProduct μ).expect
          (fun x => Real.exp (t * (resampleAvg μ sᶜ F x - m))) := by
  set P := FiniteLaw.independentProduct μ with hP
  set H := resampleAvg μ (insert a s)ᶜ F with hH
  have hG : resampleAvg μ sᶜ F = resampleAvg μ {a} H := by
    rw [hH, resampleAvg_resampleAvg]
    congr 1
    ext i
    simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    constructor
    · intro hi
      by_cases hia : i = a
      · exact Or.inl hia
      · exact Or.inr (fun h => h.elim hia hi)
    · rintro (hia | hia)
      · rw [hia]
        exact ha
      · exact fun h => hia (Or.inr h)
  have hHbd : ∀ x i b, |H (Function.update x i b) - H x| ≤ c i :=
    resampleAvg_update_le μ (insert a s)ᶜ F c hF
  rw [hG, ← expect_resampleAvg μ {a} (fun x => Real.exp (t * (H x - m))),
    ← FiniteLaw.expect_smul]
  apply P.expect_mono
  intro x
  set φ : (ι → α) → ℝ := fun y => H (({a} : Finset ι).piecewise y x) with hφ
  have hEφ : resampleAvg μ {a} H x = P.expect φ := rfl
  have hsplit : resampleAvg μ {a} (fun x => Real.exp (t * (H x - m))) x =
      Real.exp (t * (P.expect φ - m)) *
        P.expect (fun y => Real.exp (t * (φ y - P.expect φ))) := by
    rw [← FiniteLaw.expect_smul]
    apply P.expect_congr
    intro y
    show Real.exp (t * (φ y - m)) =
      Real.exp (t * (P.expect φ - m)) * Real.exp (t * (φ y - P.expect φ))
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, hEφ, mul_comm (Real.exp (t ^ 2 * c a ^ 2 / 8))]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  obtain ⟨y₀, -, hy₀⟩ := Finset.exists_min_image Finset.univ φ ⟨x, Finset.mem_univ x⟩
  have hφy : ∀ y, φ y = H (Function.update x a (y a)) := by
    intro y
    simp only [hφ, Finset.piecewise_singleton]
  have hrange : ∀ y, φ y ∈ Set.Icc (φ y₀) (φ y₀ + c a) := by
    intro y
    refine ⟨hy₀ y (Finset.mem_univ y), ?_⟩
    have h1 := hHbd (Function.update x a (y₀ a)) a (y a)
    rw [Function.update_idem] at h1
    rw [hφy y, hφy y₀]
    linarith [le_abs_self (H (Function.update x a (y a)) - H (Function.update x a (y₀ a)))]
  calc P.expect (fun y => Real.exp (t * (φ y - P.expect φ)))
      ≤ Real.exp (t ^ 2 * (φ y₀ + c a - φ y₀) ^ 2 / 8) := hoeffding_lemma P φ hrange t
    _ = Real.exp (t ^ 2 * c a ^ 2 / 8) := by rw [add_sub_cancel_left]

/-- **Bounded-differences MGF bound**: `E exp(t (F - E F)) ≤ exp(t² ∑ c_i² / 8)`. -/
theorem mcdiarmid_mgf (μ : ι → FiniteLaw α) (F : (ι → α) → ℝ) (c : ι → ℝ)
    (hF : ∀ x i a, |F (Function.update x i a) - F x| ≤ c i) (t : ℝ) :
    (FiniteLaw.independentProduct μ).expect
        (fun x => Real.exp (t * (F x - (FiniteLaw.independentProduct μ).expect F))) ≤
      Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
  have key : ∀ s : Finset ι,
      (FiniteLaw.independentProduct μ).expect (fun x => Real.exp
          (t * (resampleAvg μ sᶜ F x - (FiniteLaw.independentProduct μ).expect F))) ≤
        Real.exp (t ^ 2 * (∑ i ∈ s, c i ^ 2) / 8) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.compl_empty, resampleAvg_univ, sub_self, mul_zero, Real.exp_zero,
        FiniteLaw.expect_one, Finset.sum_empty, zero_div]
      exact le_refl _
    | insert a s ha ih =>
      calc (FiniteLaw.independentProduct μ).expect (fun x => Real.exp
            (t * (resampleAvg μ (insert a s)ᶜ F x - (FiniteLaw.independentProduct μ).expect F)))
          ≤ Real.exp (t ^ 2 * c a ^ 2 / 8) *
              (FiniteLaw.independentProduct μ).expect (fun x => Real.exp
                (t * (resampleAvg μ sᶜ F x - (FiniteLaw.independentProduct μ).expect F))) :=
            mcdiarmid_step μ F c hF s a ha _ t
        _ ≤ Real.exp (t ^ 2 * c a ^ 2 / 8) * Real.exp (t ^ 2 * (∑ i ∈ s, c i ^ 2) / 8) :=
            mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _ = Real.exp (t ^ 2 * (∑ i ∈ insert a s, c i ^ 2) / 8) := by
            rw [← Real.exp_add, Finset.sum_insert ha]
            congr 1
            ring
  have h := key Finset.univ
  rw [Finset.compl_univ, resampleAvg_empty] at h
  exact h

/-- **McDiarmid's inequality**, upper tail. -/
theorem mcdiarmid_upper (μ : ι → FiniteLaw α) (F : (ι → α) → ℝ) (c : ι → ℝ)
    (hF : ∀ x i a, |F (Function.update x i a) - F x| ≤ c i) {t : ℝ} (ht : 0 < t) :
    (FiniteLaw.independentProduct μ).prob
        {x | (FiniteLaw.independentProduct μ).expect F + t ≤ F x} ≤
      Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2) := by
  set P := FiniteLaw.independentProduct μ with hP
  set C := ∑ i, c i ^ 2 with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun i _ => sq_nonneg (c i))
  rcases hC0.eq_or_lt with hCz | hCpos
  · rw [← hCz, div_zero, Real.exp_zero]
    exact P.prob_le_one _
  have hCne : C ≠ 0 := hCpos.ne'
  set lam := 4 * t / C with hlam
  have hlam0 : 0 < lam := by positivity
  have hsub : {x | P.expect F + t ≤ F x} ⊆
      {x | Real.exp (lam * t) ≤ Real.exp (lam * (F x - P.expect F))} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hlam0.le
    linarith
  calc P.prob {x | P.expect F + t ≤ F x}
      ≤ P.prob {x | Real.exp (lam * t) ≤ Real.exp (lam * (F x - P.expect F))} :=
        prob_le_of_subset P hsub
    _ ≤ P.expect (fun x => Real.exp (lam * (F x - P.expect F))) / Real.exp (lam * t) :=
        P.markov (fun x => (Real.exp_pos _).le) (Real.exp_pos _)
    _ ≤ Real.exp (lam ^ 2 * C / 8) / Real.exp (lam * t) := by
        gcongr
        exact mcdiarmid_mgf μ F c hF lam
    _ = Real.exp (-2 * t ^ 2 / C) := by
        rw [← Real.exp_sub]
        congr 1
        rw [hlam]
        field_simp
        ring

/-- **McDiarmid's inequality**, lower tail. -/
theorem mcdiarmid_lower (μ : ι → FiniteLaw α) (F : (ι → α) → ℝ) (c : ι → ℝ)
    (hF : ∀ x i a, |F (Function.update x i a) - F x| ≤ c i) {t : ℝ} (ht : 0 < t) :
    (FiniteLaw.independentProduct μ).prob
        {x | F x ≤ (FiniteLaw.independentProduct μ).expect F - t} ≤
      Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2) := by
  have hF' : ∀ x i a, |(fun x => -F x) (Function.update x i a) - (fun x => -F x) x| ≤ c i := by
    intro x i a
    simp only
    rw [neg_sub_neg, abs_sub_comm]
    exact hF x i a
  have h := mcdiarmid_upper μ (fun x => -F x) c hF' ht
  rw [FiniteLaw.expect_neg] at h
  refine le_trans (le_of_eq ?_) h
  apply prob_congr
  intro x
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro hx <;> linarith

end McDiarmid

end SparseStack
