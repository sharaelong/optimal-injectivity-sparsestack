import SparseStack.External.Heidary
import SparseStack.External.SelectorCoupling
import SparseStack.Bridge.StackNumerics

/-!
# The full-stack moment bound (paper, Lemma `lem:numerical-refinements`, eq. (stack-moment),
lines 788–828)

For a fixed isometry `U ∈ ℝ^{n×D}`, `b ≥ 2`, `s ≥ 1`, `p ≥ 1`, with `G = (Π_{s,b} U)ᵀ(Π_{s,b} U)`:
`E ‖G - I_D‖^{2p} ≤ D [34 (√((D+2p+1)/(bs)) + (D+2p+1)/(bs) + (2p+1)/s)]^{2p}`.

Proof: `‖·‖^{2p} ≤ tr(·^{2p})` (`SparseFock.MatrixTail.opNorm_even_pow_le_trace`; `G - I` is
symmetric, being Heidary's `gramError` of the frame `MatrixFrameBridge.frameOfMatrix U hU` by
W-HEID's `SparseStack/Bridge/SketchRaw.lean`); the selector-to-iid coupling
`selector_to_iid_trace_moment` (`SparseStack/External/SelectorCoupling.lean`, Heidary's verified
`MomentTransfer.raw_trace_moment_le_scaled_product`, factor `c_b^{4p}`); `heidary_eq83_all_q`;
`c_b < 19/12`, `(19/12)² · 3(3+√2) < 34` (`SparseStack/Bridge/StackNumerics.lean`). No case
split on `D` is needed: for `D = 0` every step holds with both sides `0`.
-/

namespace SparseStack

open SparseFock
open scoped Matrix.Norms.L2Operator

/-- eq. (stack-moment). -/
theorem stack_moment {s b n D : ℕ} (hs : 1 ≤ s) (hb : 2 ≤ b) (U : Matrix (Fin n) (Fin D) ℝ)
    (hU : U.transpose * U = 1) (p : ℕ) (hp : 1 ≤ p) :
    (sketchLaw s b n (by omega)).expect
        (fun ω => ‖(sketchMatrix ω * U).transpose * (sketchMatrix ω * U) - 1‖ ^ (2 * p)) ≤
      (D : ℝ) * (34 * (Real.sqrt (((D : ℝ) + 2 * p + 1) / ((b : ℝ) * s)) +
        ((D : ℝ) + 2 * p + 1) / ((b : ℝ) * s) + (2 * (p : ℝ) + 1) / s)) ^ (2 * p) := by
  have hs0 : 0 < s := by omega
  have hb1 : 1 < b := by omega
  have hb0 : 0 < b := by omega
  -- `‖G - I‖^{2p} ≤ tr((G - I)^{2p})`; `G - I` is symmetric (it is Heidary's Gram error)
  have hpt : ∀ ω : SketchSample s b n,
      ‖(sketchMatrix ω * U).transpose * (sketchMatrix ω * U) - 1‖ ^ (2 * p) ≤
        (((sketchMatrix ω * U).transpose * (sketchMatrix ω * U) - 1) ^ (2 * p)).trace := by
    intro ω
    have hH : ((sketchMatrix ω * U).transpose * (sketchMatrix ω * U) - 1).IsHermitian := by
      rw [HeidBridge.sketch_gram_sub_one_eq U hU ω]
      exact MatrixTail.sparseStack_gramError_isHermitian _ _
    exact MatrixTail.opNorm_even_pow_le_trace _ hH p (by omega)
  calc (sketchLaw s b n hb0).expect
        (fun ω => ‖(sketchMatrix ω * U).transpose * (sketchMatrix ω * U) - 1‖ ^ (2 * p))
      ≤ (sketchLaw s b n hb0).expect (fun ω =>
          (((sketchMatrix ω * U).transpose * (sketchMatrix ω * U) - 1) ^ (2 * p)).trace) :=
        FiniteLaw.expect_mono _ hpt
    _ ≤ SparseIIDCoupling.cB b ^ (4 * p) * (ProductFock.iidLaw b hb1 (s * b) n).expect
          (fun ω => ((VacuumMoment.iidGramError b (MatrixFrameBridge.frameOfMatrix U hU) ω) ^
            (2 * p)).trace) :=
        selector_to_iid_trace_moment hs hb U hU p
    _ ≤ SparseIIDCoupling.cB b ^ (4 * p) * ((D : ℝ) *
          (3 * PaperParameters.betaEnvelope D p (((s * b : ℕ) : ℝ)) (s : ℝ)) ^ (2 * p)) := by
        apply mul_le_mul_of_nonneg_left (External.heidary_eq83_all_q hs0 hb1 _)
        exact pow_nonneg (le_trans zero_le_one (SparseIIDCoupling.one_le_cB hb0)) _
    _ ≤ (D : ℝ) * (34 * (Real.sqrt (((D : ℝ) + 2 * p + 1) / ((b : ℝ) * s)) +
          ((D : ℝ) + 2 * p + 1) / ((b : ℝ) * s) + (2 * (p : ℝ) + 1) / s)) ^ (2 * p) :=
        StackBridge.stack_moment_numeric hb0

end SparseStack
