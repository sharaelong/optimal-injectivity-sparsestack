import SparseStack.Prob.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Hoeffding's lemma for finite laws (contract 1)

Paper, Section 3, display (2): if a centered random variable is supported in an interval of
length `c`, then `log E e^{tU} ≤ t²c²/8`.

Proof plan: transport the finite law to the probability measure `PMF.toMeasure` of the
corresponding `PMF` on `α` (with the discrete σ-algebra), where integrals are the same finite
sums (`PMF.integral_eq_sum`), and apply Mathlib's Hoeffding lemma
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`.
-/

open scoped BigOperators

namespace SparseStack

open SparseFock

/-- **Hoeffding's lemma** for a finite law: if `f` takes values in `[a, b]`, then the
centered moment generating function satisfies `E exp(t (f - E f)) ≤ exp(t² (b - a)² / 8)`. -/
theorem hoeffding_lemma {α : Type*} [Fintype α] (μ : FiniteLaw α) (f : α → ℝ) {a b : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc a b) (t : ℝ) :
    μ.expect (fun x => Real.exp (t * (f x - μ.expect f))) ≤
      Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  let _ : MeasurableSpace α := ⊤
  have hsum : ∑ x, ENNReal.ofReal (μ.weight x) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => μ.weight_nonneg x), μ.sum_weight,
      ENNReal.ofReal_one]
  set p : PMF α := PMF.ofFintype (fun x => ENNReal.ofReal (μ.weight x)) hsum with hp
  have hInt : ∀ g : α → ℝ, ∫ x, g x ∂p.toMeasure = μ.expect g := by
    intro g
    rw [PMF.integral_eq_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [hp, PMF.ofFintype_apply, ENNReal.toReal_ofReal (μ.weight_nonneg x), smul_eq_mul]
  have hm : AEMeasurable f p.toMeasure := Measurable.of_discrete.aemeasurable
  have hb : ∀ᵐ x ∂p.toMeasure, f x ∈ Set.Icc a b := Filter.Eventually.of_forall hf
  have h := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hm hb).mgf_le t
  simp only [ProbabilityTheory.mgf] at h
  rw [hInt f, hInt] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
  rw [div_pow, sq_abs]
  ring

end SparseStack
