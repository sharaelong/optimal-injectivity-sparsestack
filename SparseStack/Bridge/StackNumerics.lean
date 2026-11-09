import SparseFockFormal.SparseIIDCoupling
import SparseFockFormal.PaperParameters

/-!
# Numerics for eq. (stack-moment)

Paper, proof of Lemma `lem:numerical-refinements` (lines 812–821): `c_b < 19/12` and
`(19/12)² · 3(3 + √2) < 34`. We use Heidary's certified bounds `c_b ≤ c⋆ < 791/500 < 19/12`
(`SparseIIDCoupling.cB_le_cStar`, `PaperParameters.cStar_lt_1582`) and `√2 < 71/50`, so that
`c_b² · 3(3 + √2) < (791/500)² · 3 · (221/50) ≈ 33.19 < 34`.

`stack_moment_numeric` converts Heidary's bound `c_b^{4p} · d (3 β_p)^{2p}` (with
`β_p = (3 + √2)(√(D_p/m) + D_p/m + (2p+1)/s)`, `m = s b`) into the paper's bracket
`D [34 (√((D+2p+1)/(bs)) + (D+2p+1)/(bs) + (2p+1)/s)]^{2p}`.
-/

namespace SparseStack.StackBridge

open SparseFock

/-- `c_b² · 3 (3 + √2) < 34`. -/
theorem cB_sq_mul_three_Cband_lt {b : ℕ} (hb : 0 < b) :
    SparseIIDCoupling.cB b ^ 2 * (3 * PaperParameters.Cband) < 34 := by
  have h1 := SparseIIDCoupling.one_le_cB hb
  have h2 := SparseIIDCoupling.cB_le_cStar hb
  have h3 := PaperParameters.cStar_lt_1582
  have h4 := PaperParameters.sqrt_two_lt_142
  have hC : PaperParameters.Cband < 221 / 50 := by
    rw [PaperParameters.Cband]
    linarith
  have hCpos := PaperParameters.Cband_pos
  have hcb : SparseIIDCoupling.cB b < 791 / 500 := lt_of_le_of_lt h2 h3
  have hcb2 : SparseIIDCoupling.cB b ^ 2 < (791 / 500) ^ 2 := by nlinarith
  nlinarith

/-- Heidary's envelope bound after the convex-order factor `c_b^{4p}` is at most the paper's
bracket in eq. (stack-moment). -/
theorem stack_moment_numeric {s b D p : ℕ} (hb : 0 < b) :
    SparseIIDCoupling.cB b ^ (4 * p) *
        ((D : ℝ) * (3 * PaperParameters.betaEnvelope D p (((s * b : ℕ) : ℝ)) (s : ℝ)) ^ (2 * p)) ≤
      (D : ℝ) * (34 * (Real.sqrt (((D : ℝ) + 2 * p + 1) / ((b : ℝ) * s)) +
        ((D : ℝ) + 2 * p + 1) / ((b : ℝ) * s) + (2 * (p : ℝ) + 1) / s)) ^ (2 * p) := by
  set X : ℝ := Real.sqrt (((D : ℝ) + 2 * p + 1) / ((b : ℝ) * s)) +
    ((D : ℝ) + 2 * p + 1) / ((b : ℝ) * s) + (2 * (p : ℝ) + 1) / s with hX
  have hX0 : 0 ≤ X := by positivity
  have hβ : PaperParameters.betaEnvelope D p (((s * b : ℕ) : ℝ)) (s : ℝ) =
      PaperParameters.Cband * X := by
    rw [PaperParameters.betaEnvelope, PaperParameters.cast_Dq, hX]
    push_cast
    rw [mul_comm (s : ℝ) (b : ℝ)]
  rw [hβ]
  have hcB := cB_sq_mul_three_Cband_lt hb
  have hCpos := PaperParameters.Cband_pos
  have hpow : SparseIIDCoupling.cB b ^ (4 * p) = (SparseIIDCoupling.cB b ^ 2) ^ (2 * p) := by
    rw [← pow_mul]
    congr 1
    ring
  calc SparseIIDCoupling.cB b ^ (4 * p) *
        ((D : ℝ) * (3 * (PaperParameters.Cband * X)) ^ (2 * p))
      = (D : ℝ) *
          (SparseIIDCoupling.cB b ^ 2 * (3 * PaperParameters.Cband) * X) ^ (2 * p) := by
        rw [hpow, mul_pow (SparseIIDCoupling.cB b ^ 2 * (3 * PaperParameters.Cband)) X,
          mul_pow (SparseIIDCoupling.cB b ^ 2) (3 * PaperParameters.Cband),
          show 3 * (PaperParameters.Cband * X) = (3 * PaperParameters.Cband) * X by ring,
          mul_pow (3 * PaperParameters.Cband) X]
        ring
    _ ≤ (D : ℝ) * (34 * X) ^ (2 * p) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D)
        apply pow_le_pow_left₀
          (mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hX0)
        exact mul_le_mul_of_nonneg_right hcB.le hX0

end SparseStack.StackBridge
