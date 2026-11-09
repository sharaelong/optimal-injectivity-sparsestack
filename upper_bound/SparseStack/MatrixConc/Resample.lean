import Mathlib
import SparseFockFormal.FiniteProbability

/-!
# Resampling one coordinate of an independent product law

For the literal independent product law `independentProduct μ` on `ι → Ω` and a coordinate `a`,
`E[h] = E[x ↦ ∑ ω, μ_a(ω) h(update x a ω)]`: one may replace the `a`-th coordinate by an
independent fresh sample. This is the only independence statement needed for the
Ahlswede–Winter iteration.

Proof: the weights satisfy `w x * μ_a ω = μ_a (x a) * w (update x a ω)`, and
`(x, ω) ↦ (update x a ω, x a)` is an involution of `(ι → Ω) × Ω`.
-/

namespace SparseStack

namespace MatrixConc

open SparseFock

variable {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω]

/-- The involution `(x, ω) ↦ (update x a ω, x a)` of `(ι → Ω) × Ω`. -/
def swapCoord (a : ι) (p : (ι → Ω) × Ω) : (ι → Ω) × Ω :=
  (Function.update p.1 a p.2, p.1 a)

omit [Fintype ι] [Fintype Ω] in
theorem swapCoord_involutive (a : ι) : Function.Involutive (swapCoord (Ω := Ω) a) := by
  intro p
  simp only [swapCoord, Function.update_idem, Function.update_eq_self, Function.update_self]

/-- Fiber identity: `∑ x, ∑ ω, F (update x a ω) (x a) = ∑ y, ∑ ω, F y ω`. -/
theorem sum_update_fiber (a : ι) (F : (ι → Ω) → Ω → ℝ) :
    ∑ x : ι → Ω, ∑ ω : Ω, F (Function.update x a ω) (x a) = ∑ y : ι → Ω, ∑ ω : Ω, F y ω := by
  have h := Equiv.sum_comp (swapCoord_involutive (Ω := Ω) a).toPerm
    (fun q : (ι → Ω) × Ω => F q.1 q.2)
  simpa only [Fintype.sum_prod_type, Function.Involutive.coe_toPerm, swapCoord] using h

/-- **Resampling lemma** for the independent product law. -/
theorem expect_resample (μ : ι → FiniteLaw Ω) (a : ι) (h : (ι → Ω) → ℝ) :
    (FiniteLaw.independentProduct μ).expect h =
      (FiniteLaw.independentProduct μ).expect
        (fun x => ∑ ω, (μ a).weight ω * h (Function.update x a ω)) := by
  have hweight : ∀ (x : ι → Ω) (ω : Ω),
      (∏ i, (μ i).weight (x i)) * (μ a).weight ω =
        (μ a).weight (x a) * ∏ i, (μ i).weight (Function.update x a ω i) := by
    intro x ω
    have e1 : (∏ i, (μ i).weight (x i)) =
        (μ a).weight (x a) * ∏ i ∈ Finset.univ.erase a, (μ i).weight (x i) :=
      (Finset.mul_prod_erase _ (fun i => (μ i).weight (x i)) (Finset.mem_univ a)).symm
    have e2 : (∏ i, (μ i).weight (Function.update x a ω i)) =
        (μ a).weight ω * ∏ i ∈ Finset.univ.erase a, (μ i).weight (x i) := by
      rw [← Finset.mul_prod_erase _ (fun i => (μ i).weight (Function.update x a ω i))
        (Finset.mem_univ a)]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [e1, e2]
    ring
  simp only [FiniteLaw.expect, FiniteLaw.independentProduct_weight]
  symm
  calc ∑ x : ι → Ω, (∏ i, (μ i).weight (x i)) *
        ∑ ω, (μ a).weight ω * h (Function.update x a ω)
      = ∑ x : ι → Ω, ∑ ω, (μ a).weight (x a) *
          ((∏ i, (μ i).weight (Function.update x a ω i)) * h (Function.update x a ω)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        rw [← mul_assoc, ← mul_assoc, hweight x ω, mul_assoc]
    _ = ∑ y : ι → Ω, ∑ ω, (μ a).weight ω * ((∏ i, (μ i).weight (y i)) * h y) :=
        sum_update_fiber a (fun y ω => (μ a).weight ω * ((∏ i, (μ i).weight (y i)) * h y))
    _ = ∑ y : ι → Ω, (∏ i, (μ i).weight (y i)) * h y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [← Finset.sum_mul, (μ a).sum_weight, one_mul]

end MatrixConc

end SparseStack
