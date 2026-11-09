import Osi.Spec
import Osi.Prelim.SubspaceSing
import Osi.LowerBound.RowPreprocess
import Osi.LowerBound.C4Subgraph
import Osi.LowerBound.TreeCancel
import Osi.LowerBound.TuranCenters
import Osi.LowerBound.HallReservoirs
import Osi.LowerBound.CoordReduction
import Osi.LowerBound.Endgame
import Osi.UpperBound.OverlapProp
import Osi.UpperBound.GeneralParams
import Osi.UpperBound.Sec234
import Osi.UpperBound.Sec5
import Osi.UpperBound.Sec6

/-!
# Headline Proofs of All Paper Theorems (`0 sorry`)

Proves every `Prop`-valued theorem, proposition, and lemma declared in `Osi/Spec.lean` across
Sections 1–10 with literal `Osi.Spec.*` types, culminating in `Osi.Headline.allPaperTheorems`.
-/

namespace Osi.Headline

theorem theorem_1_1_GeneralParams : Osi.Spec.Theorem_1_1_GeneralParams :=
  Osi.UpperBound.theorem_1_1_GeneralParams

theorem theorem_1_1_PaperRange : Osi.Spec.Theorem_1_1_PaperRange :=
  Osi.UpperBound.theorem_1_1_PaperRange

theorem theorem_1_1_Schedule : Osi.Spec.Theorem_1_1_Schedule :=
  Osi.UpperBound.theorem_1_1_Schedule

theorem proposition_SparseStack_Overlap : Osi.Spec.Proposition_SparseStack_Overlap :=
  Osi.UpperBound.proposition_SparseStack_Overlap

theorem theorem_1_3_LowerBound_HalfProb : Osi.Spec.Theorem_1_3_LowerBound_HalfProb :=
  Osi.LowerBound.theorem_1_3_LowerBound_HalfProb

theorem theorem_1_3_LowerBound : Osi.Spec.Theorem_1_3_LowerBound :=
  Osi.LowerBound.theorem_1_3_LowerBound

theorem theorem_1_3_QuadraticN : Osi.Spec.Theorem_1_3_QuadraticN :=
  Osi.LowerBound.theorem_1_3_QuadraticN

theorem theorem_1_3_NecessityOfAmbientBound : Osi.Spec.Theorem_1_3_NecessityOfAmbientBound :=
  Osi.Prelim.theorem_1_3_NecessityOfAmbientBound

theorem theorem_Optimal_SparseStack_Tightness : Osi.Spec.Theorem_Optimal_SparseStack_Tightness :=
  Osi.UpperBound.theorem_Optimal_SparseStack_Tightness

theorem theorem_2_1_FlatPreservation : Osi.Spec.Theorem_2_1_FlatPreservation :=
  Osi.UpperBound.theorem_2_1_FlatPreservation

theorem theorem_2_2_CommonSupport : Osi.Spec.Theorem_2_2_CommonSupport :=
  Osi.UpperBound.theorem_2_2_CommonSupport

theorem theorem_2_3_HeavyPreservation : Osi.Spec.Theorem_2_3_HeavyPreservation :=
  Osi.UpperBound.theorem_2_3_HeavyPreservation

theorem lemma_3_2_WeightedBernoulli : Osi.Spec.Lemma_3_2_WeightedBernoulli :=
  Osi.UpperBound.lemma_3_2_WeightedBernoulli

theorem lemma_3_3_PointwiseFlat : Osi.Spec.Lemma_3_3_PointwiseFlat :=
  Osi.UpperBound.lemma_3_3_PointwiseFlat

theorem lemma_3_4_LatticeRounding : Osi.Spec.Lemma_3_4_LatticeRounding :=
  Osi.UpperBound.lemma_3_4_LatticeRounding

theorem lemma_4_1_GaussianTruncation : Osi.Spec.Lemma_4_1_GaussianTruncation :=
  Osi.UpperBound.lemma_4_1_GaussianTruncation

theorem lemma_4_2_MinimaxSelection : Osi.Spec.Lemma_4_2_MinimaxSelection :=
  Osi.UpperBound.lemma_4_2_MinimaxSelection

theorem lemma_5_3_IidOpNorm : Osi.Spec.Lemma_5_3_IidOpNorm :=
  Osi.UpperBound.lemma_5_3_IidOpNorm

theorem lemma_5_4_IsolatedCrossTerm : Osi.Spec.Lemma_5_4_IsolatedCrossTerm :=
  Osi.UpperBound.lemma_5_4_IsolatedCrossTerm

theorem lemma_5_5_FullSketchMoment : Osi.Spec.Lemma_5_5_FullSketchMoment :=
  Osi.UpperBound.lemma_5_5_FullSketchMoment

theorem lemma_6_1_SingleGroup : Osi.Spec.Lemma_6_1_SingleGroup :=
  Osi.UpperBound.lemma_6_1_SingleGroup

theorem lemma_6_2_TwoGroupIsolation : Osi.Spec.Lemma_6_2_TwoGroupIsolation :=
  Osi.UpperBound.lemma_6_2_TwoGroupIsolation

theorem lemma_6_3_TwoGroupHeavy : Osi.Spec.Lemma_6_3_TwoGroupHeavy :=
  Osi.UpperBound.lemma_6_3_TwoGroupHeavy

theorem lemma_8_1_HeavyRowCount : Osi.Spec.Lemma_8_1_HeavyRowCount :=
  Osi.LowerBound.lemma_8_1_HeavyRowCount

theorem lemma_8_2_SmallOrOneSparseElim : Osi.Spec.Lemma_8_2_SmallOrOneSparseElim :=
  Osi.LowerBound.lemma_8_2_SmallOrOneSparseElim

theorem lemma_8_3_C4FreeSubgraph : Osi.Spec.Lemma_8_3_C4FreeSubgraph :=
  Osi.LowerBound.lemma_8_3_C4FreeSubgraph

theorem lemma_9_1_TreeCancellation : Osi.Spec.Lemma_9_1_TreeCancellation :=
  Osi.LowerBound.lemma_9_1_TreeCancellation

theorem lemma_9_2_SingleTreeDisjointLeaves : Osi.Spec.Lemma_9_2_SingleTreeDisjointLeaves :=
  Osi.LowerBound.lemma_9_2_SingleTreeDisjointLeaves

theorem lemma_9_3_TuranCaroWei : Osi.Spec.Lemma_9_3_TuranCaroWei :=
  Osi.LowerBound.lemma_9_3_TuranCaroWei

theorem lemma_9_4_TuranCenterRows : Osi.Spec.Lemma_9_4_TuranCenterRows :=
  Osi.LowerBound.lemma_9_4_TuranCenterRows

theorem lemma_9_5_HallMarriage : Osi.Spec.Lemma_9_5_HallMarriage :=
  Osi.LowerBound.lemma_9_5_HallMarriage

theorem lemma_9_6_DisjointLeafReservoirs : Osi.Spec.Lemma_9_6_DisjointLeafReservoirs :=
  Osi.LowerBound.lemma_9_6_DisjointLeafReservoirs

theorem theorem_9_7_WitnessForest : Osi.Spec.Theorem_9_7_WitnessForest :=
  Osi.LowerBound.theorem_9_7_WitnessForest

theorem lemma_10_1_CoordinateSubspaceReduction : Osi.Spec.Lemma_10_1_CoordinateSubspaceReduction :=
  Osi.LowerBound.lemma_10_1_CoordinateSubspaceReduction

theorem theorem_10_2_FiniteScale : Osi.Spec.Theorem_10_2_FiniteScale :=
  Osi.LowerBound.theorem_10_2_FiniteScale

/-- Complete certification of all 35 statements in `Osi.Spec.AllPaperTheorems`. -/
theorem allPaperTheorems : Osi.Spec.AllPaperTheorems :=
  ⟨theorem_1_1_GeneralParams,
   theorem_1_1_PaperRange,
   theorem_1_1_Schedule,
   proposition_SparseStack_Overlap,
   theorem_1_3_LowerBound_HalfProb,
   theorem_1_3_LowerBound,
   theorem_1_3_QuadraticN,
   theorem_1_3_NecessityOfAmbientBound,
   theorem_Optimal_SparseStack_Tightness,
   theorem_2_1_FlatPreservation,
   theorem_2_2_CommonSupport,
   theorem_2_3_HeavyPreservation,
   lemma_3_2_WeightedBernoulli,
   lemma_3_3_PointwiseFlat,
   lemma_3_4_LatticeRounding,
   lemma_4_1_GaussianTruncation,
   lemma_4_2_MinimaxSelection,
   lemma_5_3_IidOpNorm,
   lemma_5_4_IsolatedCrossTerm,
   lemma_5_5_FullSketchMoment,
   lemma_6_1_SingleGroup,
   lemma_6_2_TwoGroupIsolation,
   lemma_6_3_TwoGroupHeavy,
   lemma_8_1_HeavyRowCount,
   lemma_8_2_SmallOrOneSparseElim,
   lemma_8_3_C4FreeSubgraph,
   lemma_9_1_TreeCancellation,
   lemma_9_2_SingleTreeDisjointLeaves,
   lemma_9_3_TuranCaroWei,
   lemma_9_4_TuranCenterRows,
   lemma_9_5_HallMarriage,
   lemma_9_6_DisjointLeafReservoirs,
   theorem_9_7_WitnessForest,
   lemma_10_1_CoordinateSubspaceReduction,
   theorem_10_2_FiniteScale⟩

end Osi.Headline
