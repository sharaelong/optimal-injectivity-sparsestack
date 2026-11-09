import OsiUb.Gate
import OsiUb.Headline
import SparseStack.Main

/-!
# G1 Integration Gate for `OsiUb` (`OsiUb/GateCheck.lean`)

Runs the elaborated trust gate (`OsiUb/Gate.lean`) on:
1. the cone of `OsiUb.Headline.allUpperBoundTheorems` and all 28 individual `OsiUb.Headline.*`
   theorems,
2. every constant of every `OsiUb`, `SparseStack`, and `SparseFockFormal` module in scope
   (`#osi_gate_modules OsiUb SparseStack SparseFockFormal`),
3. cross-check against `Lean.CollectAxioms` (`#osi_gate_crosscheck_modules`),
4. `#print axioms` on `OsiUb.Headline.allUpperBoundTheorems` and the main Theorem 1.1 statements,
5. literal-type `example` checks against every `OsiUb.Spec.*` `Prop` definition.
-/

#osi_gate_check [
  OsiUb.Headline.allUpperBoundTheorems,
  OsiUb.Headline.theorem_1_1_GeneralParams,
  OsiUb.Headline.theorem_1_1_PaperRange,
  OsiUb.Headline.theorem_1_1_Schedule,
  OsiUb.Headline.proposition_SparseStack_Overlap,
  OsiUb.Headline.theorem_2_2_FlatPreservation,
  OsiUb.Headline.theorem_2_3_CommonSupport,
  OsiUb.Headline.lemma_2_4_IsolatedCrossTerm,
  OsiUb.Headline.lemma_2_4_IsolatedCrossTerm_Submatrix,
  OsiUb.Headline.theorem_2_5_HeavyPreservation,
  OsiUb.Headline.theorem_2_5_HeavyPreservation_EvenBlocks,
  OsiUb.Headline.fact_3_1_McDiarmid,
  OsiUb.Headline.lemma_3_2_WeightedBernoulli,
  OsiUb.Headline.lemma_3_2_PointwiseFlat,
  OsiUb.Headline.lemma_3_3_LatticeRounding,
  OsiUb.Headline.lemma_4_1_GaussianTruncation,
  OsiUb.Headline.lemma_4_2_MinimaxSelection,
  OsiUb.Headline.claim_4_3_MinimaxWeights,
  OsiUb.Headline.fact_5_1_HeidaryOffDiagMoment,
  OsiUb.Headline.fact_5_2_ScalarVarMatrixBernstein,
  OsiUb.Headline.lemma_5_3_IidOpNorm,
  OsiUb.Headline.claim_5_4_SingleBlockCoupling,
  OsiUb.Headline.lemma_5_5_CouplingJensen,
  OsiUb.Headline.claim_5_6_SymmetricConvexDom,
  OsiUb.Headline.lemma_5_7_FullSketchMoment,
  OsiUb.Headline.theorem_Def61_Def62_Equivalence,
  OsiUb.Headline.lemma_6_3_SingleGroup,
  OsiUb.Headline.lemma_6_3_SingleGroup_Conditional,
  OsiUb.Headline.lemma_6_4_TwoGroupIsolation
]

#osi_gate_modules OsiUb SparseStack SparseFockFormal

#osi_gate_crosscheck_modules [OsiUb, SparseStack, SparseFockFormal]

#print axioms OsiUb.Headline.allUpperBoundTheorems
#print axioms OsiUb.Headline.theorem_1_1_GeneralParams
#print axioms OsiUb.Headline.theorem_1_1_PaperRange
#print axioms OsiUb.Headline.theorem_1_1_Schedule

example : OsiUb.Spec.AllUpperBoundTheorems := OsiUb.Headline.allUpperBoundTheorems
example : OsiUb.Spec.Theorem_1_1_GeneralParams := OsiUb.Headline.theorem_1_1_GeneralParams
example : OsiUb.Spec.Theorem_1_1_PaperRange := OsiUb.Headline.theorem_1_1_PaperRange
example : OsiUb.Spec.Theorem_1_1_Schedule := OsiUb.Headline.theorem_1_1_Schedule
example : OsiUb.Spec.Proposition_SparseStack_Overlap := OsiUb.Headline.proposition_SparseStack_Overlap
example : OsiUb.Spec.Theorem_2_2_FlatPreservation := OsiUb.Headline.theorem_2_2_FlatPreservation
example : OsiUb.Spec.Theorem_2_3_CommonSupport := OsiUb.Headline.theorem_2_3_CommonSupport
example : OsiUb.Spec.Lemma_2_4_IsolatedCrossTerm := OsiUb.Headline.lemma_2_4_IsolatedCrossTerm
example : OsiUb.Spec.Lemma_2_4_IsolatedCrossTerm_Submatrix := OsiUb.Headline.lemma_2_4_IsolatedCrossTerm_Submatrix
example : OsiUb.Spec.Theorem_2_5_HeavyPreservation := OsiUb.Headline.theorem_2_5_HeavyPreservation
example : OsiUb.Spec.Theorem_2_5_HeavyPreservation_EvenBlocks := OsiUb.Headline.theorem_2_5_HeavyPreservation_EvenBlocks
example : OsiUb.Spec.Fact_3_1_McDiarmid := OsiUb.Headline.fact_3_1_McDiarmid
example : OsiUb.Spec.Lemma_3_2_WeightedBernoulli := OsiUb.Headline.lemma_3_2_WeightedBernoulli
example : OsiUb.Spec.Lemma_3_2_PointwiseFlat := OsiUb.Headline.lemma_3_2_PointwiseFlat
example : OsiUb.Spec.Lemma_3_3_LatticeRounding := OsiUb.Headline.lemma_3_3_LatticeRounding
example : OsiUb.Spec.Lemma_4_1_GaussianTruncation := OsiUb.Headline.lemma_4_1_GaussianTruncation
example : OsiUb.Spec.Lemma_4_2_MinimaxSelection := OsiUb.Headline.lemma_4_2_MinimaxSelection
example : OsiUb.Spec.Claim_4_3_MinimaxWeights := OsiUb.Headline.claim_4_3_MinimaxWeights
example : OsiUb.Spec.Fact_5_1_HeidaryOffDiagMoment := OsiUb.Headline.fact_5_1_HeidaryOffDiagMoment
example : OsiUb.Spec.Fact_5_2_ScalarVarMatrixBernstein := OsiUb.Headline.fact_5_2_ScalarVarMatrixBernstein
example : OsiUb.Spec.Lemma_5_3_IidOpNorm := OsiUb.Headline.lemma_5_3_IidOpNorm
example : OsiUb.Spec.Claim_5_4_SingleBlockCoupling := OsiUb.Headline.claim_5_4_SingleBlockCoupling
example : OsiUb.Spec.Lemma_5_5_CouplingJensen := OsiUb.Headline.lemma_5_5_CouplingJensen
example : OsiUb.Spec.Claim_5_6_SymmetricConvexDom := OsiUb.Headline.claim_5_6_SymmetricConvexDom
example : OsiUb.Spec.Lemma_5_7_FullSketchMoment := OsiUb.Headline.lemma_5_7_FullSketchMoment
example : OsiUb.Spec.Theorem_Def61_Def62_Equivalence := OsiUb.Headline.theorem_Def61_Def62_Equivalence
example : OsiUb.Spec.Lemma_6_3_SingleGroup := OsiUb.Headline.lemma_6_3_SingleGroup
example : OsiUb.Spec.Lemma_6_3_SingleGroup_Conditional := OsiUb.Headline.lemma_6_3_SingleGroup_Conditional
example : OsiUb.Spec.Lemma_6_4_TwoGroupIsolation := OsiUb.Headline.lemma_6_4_TwoGroupIsolation
