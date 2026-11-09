import OsiUb.Spec
import OsiUb.Prelim.SubspaceSing
import OsiUb.UpperBound.OverlapProp
import OsiUb.UpperBound.GeneralParams
import OsiUb.UpperBound.Sec234
import OsiUb.UpperBound.Sec5
import OsiUb.UpperBound.Sec6

/-!
# Headline Proofs of All 28 Upper-Bound Statements (`0 sorry`)

Proves every `Prop`-valued theorem, proposition, lemma, claim, and fact declared in
`OsiUb/Spec.lean` across Sections 1–7 of `constant_injectivity_sparsestack-2.pdf` with literal
`OsiUb.Spec.*` types, culminating in `OsiUb.Headline.allUpperBoundTheorems`.
-/

namespace OsiUb.Headline

theorem theorem_1_1_GeneralParams : OsiUb.Spec.Theorem_1_1_GeneralParams :=
  OsiUb.UpperBound.theorem_1_1_GeneralParams

theorem theorem_1_1_PaperRange : OsiUb.Spec.Theorem_1_1_PaperRange :=
  OsiUb.UpperBound.theorem_1_1_PaperRange

theorem theorem_1_1_Schedule : OsiUb.Spec.Theorem_1_1_Schedule :=
  OsiUb.UpperBound.theorem_1_1_Schedule

theorem proposition_SparseStack_Overlap : OsiUb.Spec.Proposition_SparseStack_Overlap :=
  OsiUb.UpperBound.proposition_SparseStack_Overlap

theorem theorem_2_2_FlatPreservation : OsiUb.Spec.Theorem_2_2_FlatPreservation :=
  OsiUb.UpperBound.theorem_2_2_FlatPreservation

theorem theorem_2_3_CommonSupport : OsiUb.Spec.Theorem_2_3_CommonSupport :=
  OsiUb.UpperBound.theorem_2_3_CommonSupport

theorem lemma_2_4_IsolatedCrossTerm : OsiUb.Spec.Lemma_2_4_IsolatedCrossTerm :=
  OsiUb.UpperBound.lemma_2_4_IsolatedCrossTerm

theorem lemma_2_4_IsolatedCrossTerm_Submatrix :
    OsiUb.Spec.Lemma_2_4_IsolatedCrossTerm_Submatrix :=
  OsiUb.UpperBound.lemma_2_4_IsolatedCrossTerm_Submatrix

theorem theorem_2_5_HeavyPreservation : OsiUb.Spec.Theorem_2_5_HeavyPreservation :=
  OsiUb.UpperBound.theorem_2_5_HeavyPreservation

theorem theorem_2_5_HeavyPreservation_EvenBlocks :
    OsiUb.Spec.Theorem_2_5_HeavyPreservation_EvenBlocks :=
  OsiUb.UpperBound.theorem_2_5_HeavyPreservation_EvenBlocks

theorem fact_3_1_McDiarmid : OsiUb.Spec.Fact_3_1_McDiarmid :=
  OsiUb.UpperBound.fact_3_1_McDiarmid

theorem lemma_3_2_WeightedBernoulli : OsiUb.Spec.Lemma_3_2_WeightedBernoulli :=
  OsiUb.UpperBound.lemma_3_2_WeightedBernoulli

theorem lemma_3_2_PointwiseFlat : OsiUb.Spec.Lemma_3_2_PointwiseFlat :=
  OsiUb.UpperBound.lemma_3_2_PointwiseFlat

theorem lemma_3_3_LatticeRounding : OsiUb.Spec.Lemma_3_3_LatticeRounding :=
  OsiUb.UpperBound.lemma_3_3_LatticeRounding

theorem lemma_4_1_GaussianTruncation : OsiUb.Spec.Lemma_4_1_GaussianTruncation :=
  OsiUb.UpperBound.lemma_4_1_GaussianTruncation

theorem lemma_4_2_MinimaxSelection : OsiUb.Spec.Lemma_4_2_MinimaxSelection :=
  OsiUb.UpperBound.lemma_4_2_MinimaxSelection

theorem claim_4_3_MinimaxWeights : OsiUb.Spec.Claim_4_3_MinimaxWeights :=
  OsiUb.UpperBound.claim_4_3_MinimaxWeights

theorem fact_5_1_HeidaryOffDiagMoment : OsiUb.Spec.Fact_5_1_HeidaryOffDiagMoment :=
  OsiUb.UpperBound.fact_5_1_HeidaryOffDiagMoment

theorem fact_5_2_ScalarVarMatrixBernstein : OsiUb.Spec.Fact_5_2_ScalarVarMatrixBernstein :=
  OsiUb.UpperBound.fact_5_2_ScalarVarMatrixBernstein

theorem lemma_5_3_IidOpNorm : OsiUb.Spec.Lemma_5_3_IidOpNorm :=
  OsiUb.UpperBound.lemma_5_3_IidOpNorm

theorem claim_5_4_SingleBlockCoupling : OsiUb.Spec.Claim_5_4_SingleBlockCoupling :=
  OsiUb.UpperBound.claim_5_4_SingleBlockCoupling

theorem lemma_5_5_CouplingJensen : OsiUb.Spec.Lemma_5_5_CouplingJensen :=
  OsiUb.UpperBound.lemma_5_5_CouplingJensen

theorem claim_5_6_SymmetricConvexDom : OsiUb.Spec.Claim_5_6_SymmetricConvexDom :=
  OsiUb.UpperBound.claim_5_6_SymmetricConvexDom

theorem lemma_5_7_FullSketchMoment : OsiUb.Spec.Lemma_5_7_FullSketchMoment :=
  OsiUb.UpperBound.lemma_5_7_FullSketchMoment

theorem theorem_Def61_Def62_Equivalence : OsiUb.Spec.Theorem_Def61_Def62_Equivalence :=
  OsiUb.UpperBound.theorem_Def61_Def62_Equivalence

theorem lemma_6_3_SingleGroup : OsiUb.Spec.Lemma_6_3_SingleGroup :=
  OsiUb.UpperBound.lemma_6_3_SingleGroup

theorem lemma_6_3_SingleGroup_Conditional : OsiUb.Spec.Lemma_6_3_SingleGroup_Conditional :=
  OsiUb.UpperBound.lemma_6_3_SingleGroup_Conditional

theorem lemma_6_4_TwoGroupIsolation : OsiUb.Spec.Lemma_6_4_TwoGroupIsolation :=
  OsiUb.UpperBound.lemma_6_4_TwoGroupIsolation

/-- Master conjunction of all 28 upper-bound theorems, propositions, lemmas, claims, and facts. -/
theorem allUpperBoundTheorems : OsiUb.Spec.AllUpperBoundTheorems :=
  ⟨theorem_1_1_GeneralParams,
    theorem_1_1_PaperRange,
    theorem_1_1_Schedule,
    proposition_SparseStack_Overlap,
    theorem_2_2_FlatPreservation,
    theorem_2_3_CommonSupport,
    lemma_2_4_IsolatedCrossTerm,
    lemma_2_4_IsolatedCrossTerm_Submatrix,
    theorem_2_5_HeavyPreservation,
    theorem_2_5_HeavyPreservation_EvenBlocks,
    fact_3_1_McDiarmid,
    lemma_3_2_WeightedBernoulli,
    lemma_3_2_PointwiseFlat,
    lemma_3_3_LatticeRounding,
    lemma_4_1_GaussianTruncation,
    lemma_4_2_MinimaxSelection,
    claim_4_3_MinimaxWeights,
    fact_5_1_HeidaryOffDiagMoment,
    fact_5_2_ScalarVarMatrixBernstein,
    lemma_5_3_IidOpNorm,
    claim_5_4_SingleBlockCoupling,
    lemma_5_5_CouplingJensen,
    claim_5_6_SymmetricConvexDom,
    lemma_5_7_FullSketchMoment,
    theorem_Def61_Def62_Equivalence,
    lemma_6_3_SingleGroup,
    lemma_6_3_SingleGroup_Conditional,
    lemma_6_4_TwoGroupIsolation⟩

end OsiUb.Headline
