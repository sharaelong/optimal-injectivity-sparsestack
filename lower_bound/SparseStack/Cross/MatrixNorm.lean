import SparseStack.Cross.Defs

/-!
# Cross-Gram bound: matrix-norm helpers (W-CROSS)

All norms are L2 operator norms (`Matrix.Norms.L2Operator`).

* `l2_opNorm_le_of_forall`: `‖A‖ ≤ c` from `‖A x‖² ≤ c² ‖x‖²` for all `x`.
* `l2_opNorm_le_sqrt_frobSq`: `‖A‖ ≤ ‖A‖_F`.
* `l2_opNorm_rowSelect_le_one`: a row-selection matrix has norm `≤ 1` (adding rows cannot decrease
  the operator norm, step (6)).
* `expectMat_eq_sum`, `norm_expectMat_le`: Jensen / triangle inequality `‖E M‖ ≤ E ‖M‖`
  (conditional Jensen of steps (2), (3)).
* `convexOn_norm_add_smul`: `r ↦ ‖C + r • D‖` is convex (step (5)).
-/

namespace SparseStack
namespace Cross

open SparseFock
open scoped Matrix.Norms.L2Operator

section

variable {m l : Type} [Fintype m] [Fintype l] [DecidableEq l]

/-- `‖A‖ ≤ c` as soon as `∑ᵢ (A x)ᵢ² ≤ c² ∑ⱼ xⱼ²` for every `x`. -/
theorem l2_opNorm_le_of_forall (A : Matrix m l ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : l → ℝ, ∑ i, (A.mulVec x) i ^ 2 ≤ c ^ 2 * ∑ j, x j ^ 2) : ‖A‖ ≤ c := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have h3 := h (WithLp.ofLp x)
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero,
    EuclideanSpace.real_norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq]
  exact h3

/-- The operator norm is at most the Frobenius norm. -/
theorem l2_opNorm_le_sqrt_frobSq (A : Matrix m l ℝ) : ‖A‖ ≤ Real.sqrt (frobSq A) := by
  have hF : 0 ≤ frobSq A :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  apply l2_opNorm_le_of_forall A (Real.sqrt_nonneg _)
  intro x
  rw [Real.sq_sqrt hF, frobSq, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- Matrix-valued expectation as a weighted sum. -/
theorem expectMat_eq_sum {α : Type*} [Fintype α] (μ : FiniteLaw α) (M : α → Matrix m l ℝ) :
    expectMat μ M = ∑ x, μ.weight x • M x := by
  ext i k
  simp [expectMat, FiniteLaw.expect, Matrix.sum_apply]

/-- Jensen for the operator norm: `‖E M‖ ≤ E ‖M‖`. -/
theorem norm_expectMat_le {α : Type*} [Fintype α] (μ : FiniteLaw α) (M : α → Matrix m l ℝ) :
    ‖expectMat μ M‖ ≤ μ.expect (fun x => ‖M x‖) := by
  rw [expectMat_eq_sum]
  calc ‖∑ x, μ.weight x • M x‖ ≤ ∑ x, ‖μ.weight x • M x‖ := norm_sum_le _ _
    _ = ∑ x, μ.weight x * ‖M x‖ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (μ.weight_nonneg x)]
    _ = μ.expect (fun x => ‖M x‖) := rfl

/-- `r ↦ ‖C + r • D‖` is convex. -/
theorem convexOn_norm_add_smul (C D : Matrix m l ℝ) :
    ConvexOn ℝ Set.univ (fun r : ℝ => ‖C + r • D‖) := by
  refine ⟨convex_univ, fun r₁ _ r₂ _ a b ha hb hab => ?_⟩
  have e : C + (a • r₁ + b • r₂) • D = a • (C + r₁ • D) + b • (C + r₂ • D) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_eq_mul, smul_eq_mul, add_smul]
    calc C + ((a * r₁) • D + (b * r₂) • D)
        = (a + b) • C + ((a * r₁) • D + (b * r₂) • D) := by rw [hab, one_smul]
      _ = a • C + (a * r₁) • D + (b • C + (b * r₂) • D) := by rw [add_smul]; abel
  show ‖C + (a • r₁ + b • r₂) • D‖ ≤ a • ‖C + r₁ • D‖ + b • ‖C + r₂ • D‖
  rw [e]
  calc ‖a • (C + r₁ • D) + b • (C + r₂ • D)‖
      ≤ ‖a • (C + r₁ • D)‖ + ‖b • (C + r₂ • D)‖ := norm_add_le _ _
    _ = a • ‖C + r₁ • D‖ + b • ‖C + r₂ • D‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
          abs_of_nonneg hb, smul_eq_mul, smul_eq_mul]

end

/-- A row-selection matrix (row `i ∈ I` picks the row `f i`, `f` injective on `I`) has operator
norm at most one. -/
theorem l2_opNorm_rowSelect_le_one {n k : ℕ} (I : Finset (Fin n)) (f : Fin n → Fin k)
    (hf : Set.InjOn f I) :
    ‖(Matrix.of fun i ℓ => if i ∈ I ∧ ℓ = f i then (1 : ℝ) else 0 :
        Matrix (Fin n) (Fin k) ℝ)‖ ≤ 1 := by
  apply l2_opNorm_le_of_forall _ zero_le_one
  intro x
  have hrow : ∀ i, (Matrix.of fun i ℓ => if i ∈ I ∧ ℓ = f i then (1 : ℝ) else 0 :
      Matrix (Fin n) (Fin k) ℝ).mulVec x i ^ 2 = if i ∈ I then x (f i) ^ 2 else 0 := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    by_cases hi : i ∈ I
    · simp [hi]
    · simp [hi]
  simp_rw [hrow]
  rw [one_pow, one_mul, Finset.sum_ite_mem, Finset.univ_inter]
  calc ∑ i ∈ I, x (f i) ^ 2 = ∑ j ∈ I.image f, x j ^ 2 :=
        (Finset.sum_image (f := fun j => x j ^ 2) hf).symm
    _ ≤ ∑ j, x j ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

end Cross
end SparseStack
