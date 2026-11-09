import SparseStack.MatrixConc.LiebThirring
import SparseStack.MatrixConc.LieTrotter

/-!
# Golden–Thompson inequality for real symmetric matrices

`tr (exp (A + B)) ≤ tr (exp A * exp B)` for real symmetric `A B`.

Proof: by the Lie product formula (`SparseStack.MatrixConc.lie_product_formula`, applied in the
Banach algebra of real matrices with the `L2` operator norm) along the subsequence `k = 2 ^ j`,
`tr ((exp (A/k) exp (B/k)) ^ k) → tr (exp (A + B))`; and by the Lieb–Thirring inequality for
powers of two (`SparseStack.MatrixConc.lieb_thirring_pow_two`) applied to the symmetric matrices
`exp (A/k)`, `exp (B/k)`, each term is at most `tr (exp (A/k) ^ k * exp (B/k) ^ k) =
tr (exp A * exp B)`.
-/

namespace SparseStack

open NormedSpace Filter Topology MatrixConc

/-- **Golden–Thompson inequality** for real symmetric matrices:
`tr (exp (A + B)) ≤ tr (exp A * exp B)`. Here `NormedSpace.exp` is the matrix exponential
(power series), which does not depend on the choice of matrix norm. -/
theorem golden_thompson {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (NormedSpace.exp (A + B)).trace ≤ (NormedSpace.exp A * NormedSpace.exp B).trace := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [Matrix.trace]
  · have := hn
    have hLie : Tendsto (fun k : ℕ => (exp ((k : ℝ)⁻¹ • A) * exp ((k : ℝ)⁻¹ • B)) ^ k) atTop
        (𝓝 (exp (A + B))) := by
      open scoped Matrix.Norms.L2Operator in
      exact lie_product_formula A B
    have hpow : Tendsto (fun j : ℕ => 2 ^ j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
    have htr := ((Matrix.traceLinearMap n ℝ ℝ).continuous_of_finiteDimensional.tendsto _).comp
      (hLie.comp hpow)
    refine le_of_tendsto' htr (fun j => ?_)
    simp only [Function.comp_def, Matrix.traceLinearMap_apply]
    have hk0 : ((2 ^ j : ℕ) : ℝ) ≠ 0 := by positivity
    have hsA : (exp (((2 ^ j : ℕ) : ℝ)⁻¹ • A)).IsHermitian :=
      (hA.smul (IsSelfAdjoint.all _)).exp
    have hsB : (exp (((2 ^ j : ℕ) : ℝ)⁻¹ • B)).IsHermitian :=
      (hB.smul (IsSelfAdjoint.all _)).exp
    have hpowA : exp (((2 ^ j : ℕ) : ℝ)⁻¹ • A) ^ (2 ^ j) = exp A := by
      rw [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hk0,
        one_smul]
    have hpowB : exp (((2 ^ j : ℕ) : ℝ)⁻¹ • B) ^ (2 ^ j) = exp B := by
      rw [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hk0,
        one_smul]
    calc ((exp (((2 ^ j : ℕ) : ℝ)⁻¹ • A) * exp (((2 ^ j : ℕ) : ℝ)⁻¹ • B)) ^ (2 ^ j)).trace
        ≤ (exp (((2 ^ j : ℕ) : ℝ)⁻¹ • A) ^ (2 ^ j) *
            exp (((2 ^ j : ℕ) : ℝ)⁻¹ • B) ^ (2 ^ j)).trace :=
          lieb_thirring_pow_two _ _ hsA hsB j
      _ = (exp A * exp B).trace := by rw [hpowA, hpowB]

end SparseStack
