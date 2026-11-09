import SparseStack.Prob.Sketch
import SparseStack.Sketch.Mean
import SparseStack.Numerics.Params

/-!
# Spec sanity lemmas (gated, not locked)

* `minEigenvalueAtLeast_iff_quadraticLowerBound`: the eigenvalue form of `λ_min(AᵀA) ≥ α` is
  equivalent to the Rayleigh form; hence `ConstantInjection ↔ ConstantInjectionQuadratic`.
* `meanIdentity_all`: `E Ω Ωᵀ = I_n` for all `s, b ≥ 1` (eq. (1)), not only at the theorem's `ζ, b`.
* `event_can_fail`: non-vacuity witness — for `r = n = 2`, `Q = I`, the sample point where both
  coordinates share all hashes and signs has `Π e₀ = Π e₁`, so `λ_min(AᵀA) = 0 < α`.
-/

namespace SparseStack

open SparseFock

/-- Eigenvalue form ⟺ Rayleigh form of `λ_min(AᵀA) ≥ α` (Courant–Fischer / spectral theorem). -/
theorem minEigenvalueAtLeast_iff_quadraticLowerBound {k r : Type} [Fintype k] [Fintype r]
    [DecidableEq r] (A : Matrix k r ℝ) (α : ℝ) :
    MinEigenvalueAtLeast A α ↔ QuadraticLowerBound A α := by
  -- Spectral theorem for the symmetric matrix `B = Aᴴ A = U D Uᵀ` (`U` orthogonal,
  -- `D = diag λ`). With `y = Uᵀ x`: `‖A x‖² = xᵀ B x = ∑ λ_i y_i²` and `‖x‖² = ∑ y_i²`.
  -- (→) is termwise; (←) takes `x = U e_j`, so that `y = e_j`.
  unfold MinEigenvalueAtLeast QuadraticLowerBound
  set hH := Matrix.isHermitian_conjTranspose_mul_self A with hHdef
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix r r ℝ, U = (hH.eigenvectorUnitary : Matrix r r ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : r → ℝ, lam = hH.eigenvalues := ⟨_, rfl⟩
  have hUU : star U * U = 1 := by
    rw [hUdef]
    exact Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := by
    rw [hUdef]
    exact Unitary.coe_mul_star_self _
  have hstar : star U = U.transpose := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hspec : A.conjTranspose * A = U * Matrix.diagonal lam * star U := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hUdef, hlam]
    exact h
  have h2 : ∀ x : r → ℝ, Matrix.vecMul x U = Matrix.mulVec (star U) x := by
    intro x
    rw [hstar, Matrix.mulVec_transpose]
  have hquad : ∀ x : r → ℝ, dotProduct (Matrix.mulVec A x) (Matrix.mulVec A x) =
      ∑ i, lam i * (Matrix.mulVec (star U) x) i ^ 2 := by
    intro x
    have h1 : dotProduct (Matrix.mulVec A x) (Matrix.mulVec A x) =
        dotProduct x (Matrix.mulVec (A.conjTranspose * A) x) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x A.conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.vecMul_transpose]
    rw [h1, hspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x U,
      h2]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hnorm : ∀ x : r → ℝ, dotProduct x x = ∑ i, (Matrix.mulVec (star U) x) i ^ 2 := by
    intro x
    calc dotProduct x x = dotProduct x (Matrix.mulVec U (Matrix.mulVec (star U) x)) := by
          rw [Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
      _ = dotProduct (Matrix.vecMul x U) (Matrix.mulVec (star U) x) :=
          Matrix.dotProduct_mulVec _ _ _
      _ = ∑ i, (Matrix.mulVec (star U) x) i ^ 2 := by
          rw [h2]
          simp only [dotProduct, sq]
  constructor
  · intro h x
    rw [hquad x, hnorm x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi : α ≤ lam i := by
      rw [hlam]
      exact h i
    exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  · intro h j
    have hx := h (Matrix.mulVec U (Pi.single j 1))
    have hy : Matrix.mulVec (star U) (Matrix.mulVec U (Pi.single j 1)) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
    rw [hquad, hnorm, hy] at hx
    have hs1 : ∑ i, (Pi.single j (1 : ℝ) : r → ℝ) i ^ 2 = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [hij]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hs2 : ∑ i, lam i * (Pi.single j (1 : ℝ) : r → ℝ) i ^ 2 = lam j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [hij]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hs1, hs2] at hx
    rw [← hlam]
    linarith

/-- The two forms of the probability clause are equivalent. -/
theorem constantInjection_iff_quadratic : ConstantInjection ↔ ConstantInjectionQuadratic := by
  have hev : ∀ (n r : ℕ) (Q : Matrix (Fin n) (Fin r) ℝ),
      (fun ω : SketchSample (numBlocks r) (numBuckets r) n =>
          MinEigenvalueAtLeast (sketchMatrix ω * Q) constAlpha) =
        (fun ω => QuadraticLowerBound (sketchMatrix ω * Q) constAlpha) := by
    intro n r Q
    funext ω
    exact propext (minEigenvalueAtLeast_iff_quadraticLowerBound _ _)
  constructor
  · intro h n r hr hrn Q hQ
    have := h n r hr hrn Q hQ
    rwa [hev n r Q] at this
  · intro h n r hr hrn Q hQ
    have := h n r hr hrn Q hQ
    rwa [← hev n r Q] at this

/-- eq. (1) in the spec's notation, for all `s, b ≥ 1`: `E Ω Ωᵀ = I_n`. -/
theorem meanIdentity_all {s b n : ℕ} (hs : 0 < s) (hb : 0 < b) :
    uniformMeanMatrix
        (fun ω : SketchSample s b n => sketchOmega ω * (sketchOmega ω).transpose) = 1 := by
  simpa [sketchOmega, Matrix.transpose_transpose] using mean_gram_eq_one (n := n) hs hb

/-- Non-vacuity witness: the probability event of `ConstantInjection` is not always true. -/
theorem event_can_fail :
    ∃ ω : SketchSample (numBlocks 2) (numBuckets 2) 2,
      ¬ MinEigenvalueAtLeast (sketchMatrix ω * (1 : Matrix (Fin 2) (Fin 2) ℝ)) constAlpha := by
  -- All hashes `0`, all signs `+1`: columns `0` and `1` of `Π` coincide, so `Π (1, -1)ᵀ = 0`,
  -- and the Rayleigh form `α ‖x‖² ≤ ‖Π x‖²` fails at `x = (1, -1)` since `α > 0`.
  have hb : 0 < numBuckets 2 := lt_of_lt_of_le (by norm_num) (two_le_numBuckets le_rfl)
  set ω : SketchSample (numBlocks 2) (numBuckets 2) 2 :=
    (fun _ _ => ⟨0, hb⟩, fun _ _ => true) with hω
  refine ⟨ω, ?_⟩
  rw [minEigenvalueAtLeast_iff_quadraticLowerBound]
  intro h
  have hx := h ![1, -1]
  have h0 : Matrix.mulVec (sketchMatrix ω * (1 : Matrix (Fin 2) (Fin 2) ℝ)) ![1, -1] = 0 := by
    ext p
    simp [hω, Matrix.mulVec, dotProduct, sketchMatrix, Fin.sum_univ_two]
  rw [h0] at hx
  have hα : (0 : ℝ) < constAlpha := by
    unfold constAlpha
    norm_num
  norm_num [dotProduct, Fin.sum_univ_two] at hx
  linarith

end SparseStack
