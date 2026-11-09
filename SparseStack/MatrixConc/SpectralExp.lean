import Mathlib

/-!
# Spectral facts about the exponential of a real symmetric matrix

For a real symmetric `A = U diag(λ) Uᵀ` (Mathlib's `eigenvectorUnitary` and `eigenvalues`):

* `exp A = U diag(e^λ) Uᵀ` (`exp_eq_spectral`), hence `tr (exp A) = ∑ e^{λ_i}` and `exp A ⪰ 0`;
* for `0 ⪯ X ⪯ 1` the eigenvalues lie in `[0, 1]`, and by convexity `e^t ≤ 1 + (e - 1) t` there,
  so for PSD `M`: `tr (M exp X) ≤ tr M + (e - 1) tr (M X)` (`trace_mul_exp_le`);
* for PSD `S` on a nonempty index type: `exp ‖S‖ ≤ tr (exp S)` (L2 operator norm,
  `exp_norm_le_trace_exp`).
-/

namespace SparseStack

namespace MatrixConc

open Matrix NormedSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exponential of a unitarily conjugated real diagonal matrix. -/
theorem exp_conj_diagonal (U : Matrix n n ℝ) (hU : star U * U = 1) (v : n → ℝ) :
    exp (U * diagonal v * star U) = U * diagonal (fun i => Real.exp (v i)) * star U := by
  have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hU
  have hunit : IsUnit U :=
    (Matrix.isUnit_iff_isUnit_det U).mpr (Matrix.isUnit_det_of_left_inverse hU)
  have hv : exp v = fun i => Real.exp (v i) := by
    funext i
    rw [Pi.coe_exp, Real.exp_eq_exp_ℝ]
  rw [← hinv, Matrix.exp_conj U (diagonal v) hunit, Matrix.exp_diagonal, hv]

/-- Spectral form of a real symmetric matrix with Mathlib's eigen-decomposition. -/
theorem spectral_eq (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal hA.eigenvalues *
      star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

/-- Spectral form of the exponential of a real symmetric matrix. -/
theorem exp_eq_spectral (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    exp A = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      diagonal (fun i => Real.exp (hA.eigenvalues i)) *
      star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
  conv_lhs => rw [spectral_eq A hA]
  exact exp_conj_diagonal _ (Unitary.coe_star_mul_self _) _

/-- `tr (exp A) = ∑ e^{λ_i}` for real symmetric `A`. -/
theorem trace_exp_eq_sum (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    (exp A).trace = ∑ i, Real.exp (hA.eigenvalues i) := by
  rw [exp_eq_spectral A hA, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
    Matrix.trace_diagonal]

/-- The exponential of a real symmetric matrix is positive semidefinite. -/
theorem posSemidef_exp (A : Matrix n n ℝ) (hA : A.IsHermitian) : (exp A).PosSemidef := by
  rw [exp_eq_spectral A hA]
  have hD : (diagonal (fun i => Real.exp (hA.eigenvalues i))).PosSemidef :=
    PosSemidef.diagonal (fun i => (Real.exp_pos _).le)
  have := hD.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix n n ℝ)
  rwa [← Matrix.star_eq_conjTranspose] at this

/-- Trace of `M` against a unitarily conjugated diagonal matrix. -/
theorem trace_mul_conj_diagonal (M V : Matrix n n ℝ) (D : n → ℝ) :
    (M * (V * diagonal D * star V)).trace = ∑ i, (star V * M * V) i i * D i := by
  rw [show M * (V * diagonal D * star V) = (M * V) * diagonal D * star V by
      simp only [mul_assoc],
    Matrix.trace_mul_cycle, ← mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]

/-- For `0 ⪯ X ⪯ 1`, every eigenvalue of `X` lies in `[0, 1]`. -/
theorem eigenvalues_mem_Icc (X : Matrix n n ℝ) (hX : X.PosSemidef) (hX1 : (1 - X).PosSemidef)
    (i : n) : 0 ≤ hX.isHermitian.eigenvalues i ∧ hX.isHermitian.eigenvalues i ≤ 1 := by
  have hXh := hX.isHermitian
  refine ⟨hX.eigenvalues_nonneg i, ?_⟩
  have hdiag : star (hXh.eigenvectorUnitary : Matrix n n ℝ) * X *
      (hXh.eigenvectorUnitary : Matrix n n ℝ) = diagonal hXh.eigenvalues := by
    have := hXh.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    exact this
  have h1 : (star (hXh.eigenvectorUnitary : Matrix n n ℝ) * (1 - X) *
      (hXh.eigenvectorUnitary : Matrix n n ℝ)).PosSemidef := by
    rw [Matrix.star_eq_conjTranspose]
    exact hX1.conjTranspose_mul_mul_same _
  have h2 : star (hXh.eigenvectorUnitary : Matrix n n ℝ) * (1 - X) *
      (hXh.eigenvectorUnitary : Matrix n n ℝ) = 1 - diagonal hXh.eigenvalues := by
    rw [Matrix.mul_sub, Matrix.sub_mul, mul_one, Unitary.coe_star_mul_self, hdiag]
  rw [h2] at h1
  have := h1.diag_nonneg (i := i)
  simpa [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq] using this

/-- Convexity of `exp` on `[0, 1]`: `e^t ≤ 1 + (e - 1) t`. -/
theorem exp_le_one_add_mul (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.exp t ≤ 1 + (Real.exp 1 - 1) * t := by
  have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) (sub_nonneg.mpr h1) h0
    (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at this
  linarith

/-- For PSD `M` and `0 ⪯ X ⪯ 1`: `tr (M exp X) ≤ tr M + (e - 1) tr (M X)`. -/
theorem trace_mul_exp_le (M X : Matrix n n ℝ) (hM : M.PosSemidef) (hX : X.PosSemidef)
    (hX1 : (1 - X).PosSemidef) :
    (M * exp X).trace ≤ M.trace + (Real.exp 1 - 1) * (M * X).trace := by
  have hXh := hX.isHermitian
  have hB : (star (hXh.eigenvectorUnitary : Matrix n n ℝ) * M *
      (hXh.eigenvectorUnitary : Matrix n n ℝ)).PosSemidef := by
    rw [Matrix.star_eq_conjTranspose]
    exact hM.conjTranspose_mul_mul_same _
  have t1 : (M * exp X).trace = ∑ i, (star (hXh.eigenvectorUnitary : Matrix n n ℝ) * M *
      (hXh.eigenvectorUnitary : Matrix n n ℝ)) i i * Real.exp (hXh.eigenvalues i) := by
    rw [exp_eq_spectral X hXh, trace_mul_conj_diagonal]
  have t2 : M.trace = ∑ i, (star (hXh.eigenvectorUnitary : Matrix n n ℝ) * M *
      (hXh.eigenvectorUnitary : Matrix n n ℝ)) i i * 1 := by
    rw [← trace_mul_conj_diagonal, Matrix.diagonal_one, mul_one,
      Unitary.mul_star_self_of_mem (SetLike.coe_mem _), mul_one]
  have t3 : (M * X).trace = ∑ i, (star (hXh.eigenvectorUnitary : Matrix n n ℝ) * M *
      (hXh.eigenvectorUnitary : Matrix n n ℝ)) i i * hXh.eigenvalues i := by
    conv_lhs => rw [spectral_eq X hXh]
    rw [trace_mul_conj_diagonal]
  rw [t1, t2, t3, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hb := hB.diag_nonneg (i := i)
  obtain ⟨h0, h1⟩ := eigenvalues_mem_Icc X hX hX1 i
  have he := exp_le_one_add_mul (hXh.eigenvalues i) h0 h1
  nlinarith

open scoped Matrix.Norms.L2Operator in
/-- The `L2` operator norm of a real symmetric matrix is the sup norm of its eigenvalues. -/
theorem l2_opNorm_eq_norm_eigenvalues (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    ‖A‖ = ‖hA.eigenvalues‖ := by
  calc
    ‖A‖ = ‖Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary
        (Matrix.diagonal ((RCLike.ofReal ∘ hA.eigenvalues) : n → ℝ))‖ :=
      congrArg norm hA.spectral_theorem
    _ = ‖hA.eigenvalues‖ := by
      rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
        Matrix.l2_opNorm_diagonal]
      rfl

open scoped Matrix.Norms.L2Operator in
/-- For PSD `S` on a nonempty index type, `exp ‖S‖ ≤ tr (exp S)` (`L2` operator norm). -/
theorem exp_norm_le_trace_exp [Nonempty n] (S : Matrix n n ℝ) (hS : S.PosSemidef) :
    Real.exp ‖S‖ ≤ (exp S).trace := by
  rw [l2_opNorm_eq_norm_eigenvalues S hS.isHermitian, trace_exp_eq_sum S hS.isHermitian]
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm hS.isHermitian.eigenvalues).1
  dsimp only at hi
  rw [← hi, Real.norm_eq_abs, abs_of_nonneg (hS.eigenvalues_nonneg i)]
  exact Finset.single_le_sum (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

end MatrixConc

end SparseStack
