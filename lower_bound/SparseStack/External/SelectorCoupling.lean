import SparseStack.Prob.Sketch
import SparseStack.Bridge.SketchRaw
import SparseFockFormal.MomentTransfer

/-!
# Selector-to-iid coupling for the spec's sketch law (statement audit, note N1)

`selector_to_iid_trace_moment`: under the spec's uniform law `sketchLaw` on
`SketchSample s b n`, the `2p`-th trace moment of the Gram error `(Π U)ᵀ (Π U) - I` is at most
`c_b^{4p}` times the corresponding trace moment of Heidary's iid Gram error under Heidary's iid
product law `ProductFock.iidLaw b _ (s * b) n`.

This is the selector-to-iid coupling of Heidary's verified library (`SparseFock.SparseIIDCoupling`,
`SparseFock.MomentTransfer.raw_trace_moment_le_scaled_product`: convex order of the selector law
below the `c_b`-scaled iid law, with the exact trace-moment transfer identities), applied to the
spec's law through W-HEID's bridge `SparseStack/Bridge/SketchRaw.lean`: our sample space is
Heidary's `RawSample` (`HeidBridge.sketchRawEquiv`), our sketch is Heidary's `stackMatrix`
(`HeidBridge.sketch_gram_sub_one_eq`), and the two uniform laws correspond
(`HeidBridge.expect_sketchLaw_eq_rawSampleLaw`). No new probabilistic argument is made here.
-/

namespace SparseStack

open SparseFock

/-- **Selector-to-iid coupling** (paper, proof of Lemma `lem:numerical-refinements`, line 825:
`G - I_D = E[c_b² F | all selectors]` and conditional Jensen), at the level of even trace
moments: `E_spec tr((ΠU)ᵀ(ΠU) - I)^{2p} ≤ c_b^{4p} · E_iid tr(E_iid^{2p})`. It is Heidary's
verified coupling (`SparseFock.MomentTransfer.raw_trace_moment_le_scaled_product`) applied to the
spec's law `sketchLaw` via the `SketchRaw` bridge. -/
theorem selector_to_iid_trace_moment {s b n D : ℕ} (hs : 1 ≤ s) (hb : 2 ≤ b)
    (U : Matrix (Fin n) (Fin D) ℝ) (hU : U.transpose * U = 1) (p : ℕ) :
    (sketchLaw s b n (by omega)).expect (fun ω =>
        (((sketchMatrix ω * U).transpose * (sketchMatrix ω * U) - 1) ^ (2 * p)).trace) ≤
      SparseFock.SparseIIDCoupling.cB b ^ (4 * p) *
        (SparseFock.ProductFock.iidLaw b (by omega) (s * b) n).expect (fun ω =>
          ((SparseFock.VacuumMoment.iidGramError b
            (SparseFock.MatrixFrameBridge.frameOfMatrix U hU) ω) ^ (2 * p)).trace) := by
  have hs0 : 0 < s := by omega
  have hb1 : 1 < b := by omega
  have hb0 : 0 < b := by omega
  calc (sketchLaw s b n hb0).expect (fun ω =>
        (((sketchMatrix ω * U).transpose * (sketchMatrix ω * U) - 1) ^ (2 * p)).trace)
      = (sketchLaw s b n hb0).expect (fun ω =>
          ((SparseStackModel.gramError (MatrixFrameBridge.frameOfMatrix U hU)
            (SparseStackDistribution.toSample (HeidBridge.sketchRawEquiv s b n ω))) ^
              (2 * p)).trace) := by
        apply FiniteLaw.expect_congr
        intro ω
        rw [HeidBridge.sketch_gram_sub_one_eq U hU ω]
    _ = (SparseStackDistribution.rawSampleLaw s b n hb0).expect (fun z =>
          ((SparseStackModel.gramError (MatrixFrameBridge.frameOfMatrix U hU)
            (SparseStackDistribution.toSample z)) ^ (2 * p)).trace) :=
        HeidBridge.expect_sketchLaw_eq_rawSampleLaw hb0 (fun z =>
          ((SparseStackModel.gramError (MatrixFrameBridge.frameOfMatrix U hU)
            (SparseStackDistribution.toSample z)) ^ (2 * p)).trace)
    _ ≤ SparseFock.SparseIIDCoupling.cB b ^ (4 * p) *
        (SparseFock.ProductFock.iidLaw b hb1 (s * b) n).expect (fun ω =>
          ((SparseFock.VacuumMoment.iidGramError b
            (SparseFock.MatrixFrameBridge.frameOfMatrix U hU) ω) ^ (2 * p)).trace) :=
        MomentTransfer.raw_trace_moment_le_scaled_product hs0 hb1 _ p

end SparseStack
