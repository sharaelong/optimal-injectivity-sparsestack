import Osi.Gate
import Osi.Headline
import SparseStack.Main

/-!
# G1 Integration Gate for `Osi` (`Osi/GateCheck.lean`)

Runs the elaborated trust gate (`Osi/Gate.lean`) on:
1. the cone of `Osi.Headline.allPaperTheorems` and all 35 individual `Osi.Headline.*` theorems,
2. every constant of every `Osi`, `SparseStack`, and `SparseFockFormal` module in scope
   (`#osi_gate_modules Osi SparseStack SparseFockFormal`),
3. cross-check against `Lean.CollectAxioms` (`#osi_gate_crosscheck_modules`),
4. `#print axioms` on `Osi.Headline.allPaperTheorems` and the main upper/lower/tightness theorems,
5. literal-type `example` checks against every `Osi.Spec.*` `Prop` definition.
-/

#osi_gate_check [
  Osi.Headline.allPaperTheorems,
  Osi.Headline.theorem_1_1_GeneralParams,
  Osi.Headline.theorem_1_1_PaperRange,
  Osi.Headline.theorem_1_1_Schedule,
  Osi.Headline.proposition_SparseStack_Overlap,
  Osi.Headline.theorem_1_3_LowerBound_HalfProb,
  Osi.Headline.theorem_1_3_LowerBound,
  Osi.Headline.theorem_1_3_QuadraticN,
  Osi.Headline.theorem_1_3_NecessityOfAmbientBound,
  Osi.Headline.theorem_Optimal_SparseStack_Tightness,
  Osi.Headline.theorem_2_1_FlatPreservation,
  Osi.Headline.theorem_2_2_CommonSupport,
  Osi.Headline.theorem_2_3_HeavyPreservation,
  Osi.Headline.lemma_3_2_WeightedBernoulli,
  Osi.Headline.lemma_3_3_PointwiseFlat,
  Osi.Headline.lemma_3_4_LatticeRounding,
  Osi.Headline.lemma_4_1_GaussianTruncation,
  Osi.Headline.lemma_4_2_MinimaxSelection,
  Osi.Headline.lemma_5_3_IidOpNorm,
  Osi.Headline.lemma_5_4_IsolatedCrossTerm,
  Osi.Headline.lemma_5_5_FullSketchMoment,
  Osi.Headline.lemma_6_1_SingleGroup,
  Osi.Headline.lemma_6_2_TwoGroupIsolation,
  Osi.Headline.lemma_6_3_TwoGroupHeavy,
  Osi.Headline.lemma_8_1_HeavyRowCount,
  Osi.Headline.lemma_8_2_SmallOrOneSparseElim,
  Osi.Headline.lemma_8_3_C4FreeSubgraph,
  Osi.Headline.lemma_9_1_TreeCancellation,
  Osi.Headline.lemma_9_2_SingleTreeDisjointLeaves,
  Osi.Headline.lemma_9_3_TuranCaroWei,
  Osi.Headline.lemma_9_4_TuranCenterRows,
  Osi.Headline.lemma_9_5_HallMarriage,
  Osi.Headline.lemma_9_6_DisjointLeafReservoirs,
  Osi.Headline.theorem_9_7_WitnessForest,
  Osi.Headline.lemma_10_1_CoordinateSubspaceReduction,
  Osi.Headline.theorem_10_2_FiniteScale
]

#osi_gate_modules Osi SparseStack SparseFockFormal

#osi_gate_crosscheck_modules [Osi, SparseStack, SparseFockFormal]

#print axioms Osi.Headline.allPaperTheorems
#print axioms Osi.Headline.theorem_1_1_GeneralParams
#print axioms Osi.Headline.theorem_1_3_LowerBound_HalfProb
#print axioms Osi.Headline.theorem_Optimal_SparseStack_Tightness

example : Osi.Spec.AllPaperTheorems := Osi.Headline.allPaperTheorems
example : Osi.Spec.Theorem_1_1_GeneralParams := Osi.Headline.theorem_1_1_GeneralParams
example : Osi.Spec.Theorem_1_1_PaperRange := Osi.Headline.theorem_1_1_PaperRange
example : Osi.Spec.Theorem_1_1_Schedule := Osi.Headline.theorem_1_1_Schedule
example : Osi.Spec.Proposition_SparseStack_Overlap := Osi.Headline.proposition_SparseStack_Overlap
example : Osi.Spec.Theorem_1_3_LowerBound_HalfProb := Osi.Headline.theorem_1_3_LowerBound_HalfProb
example : Osi.Spec.Theorem_1_3_LowerBound := Osi.Headline.theorem_1_3_LowerBound
example : Osi.Spec.Theorem_1_3_QuadraticN := Osi.Headline.theorem_1_3_QuadraticN
example : Osi.Spec.Theorem_1_3_NecessityOfAmbientBound := Osi.Headline.theorem_1_3_NecessityOfAmbientBound
example : Osi.Spec.Theorem_Optimal_SparseStack_Tightness := Osi.Headline.theorem_Optimal_SparseStack_Tightness
example : Osi.Spec.Theorem_2_1_FlatPreservation := Osi.Headline.theorem_2_1_FlatPreservation
example : Osi.Spec.Theorem_2_2_CommonSupport := Osi.Headline.theorem_2_2_CommonSupport
example : Osi.Spec.Theorem_2_3_HeavyPreservation := Osi.Headline.theorem_2_3_HeavyPreservation
example : Osi.Spec.Lemma_3_2_WeightedBernoulli := Osi.Headline.lemma_3_2_WeightedBernoulli
example : Osi.Spec.Lemma_3_3_PointwiseFlat := Osi.Headline.lemma_3_3_PointwiseFlat
example : Osi.Spec.Lemma_3_4_LatticeRounding := Osi.Headline.lemma_3_4_LatticeRounding
example : Osi.Spec.Lemma_4_1_GaussianTruncation := Osi.Headline.lemma_4_1_GaussianTruncation
example : Osi.Spec.Lemma_4_2_MinimaxSelection := Osi.Headline.lemma_4_2_MinimaxSelection
example : Osi.Spec.Lemma_5_3_IidOpNorm := Osi.Headline.lemma_5_3_IidOpNorm
example : Osi.Spec.Lemma_5_4_IsolatedCrossTerm := Osi.Headline.lemma_5_4_IsolatedCrossTerm
example : Osi.Spec.Lemma_5_5_FullSketchMoment := Osi.Headline.lemma_5_5_FullSketchMoment
example : Osi.Spec.Lemma_6_1_SingleGroup := Osi.Headline.lemma_6_1_SingleGroup
example : Osi.Spec.Lemma_6_2_TwoGroupIsolation := Osi.Headline.lemma_6_2_TwoGroupIsolation
example : Osi.Spec.Lemma_6_3_TwoGroupHeavy := Osi.Headline.lemma_6_3_TwoGroupHeavy
example : Osi.Spec.Lemma_8_1_HeavyRowCount := Osi.Headline.lemma_8_1_HeavyRowCount
example : Osi.Spec.Lemma_8_2_SmallOrOneSparseElim := Osi.Headline.lemma_8_2_SmallOrOneSparseElim
example : Osi.Spec.Lemma_8_3_C4FreeSubgraph := Osi.Headline.lemma_8_3_C4FreeSubgraph
example : Osi.Spec.Lemma_9_1_TreeCancellation := Osi.Headline.lemma_9_1_TreeCancellation
example : Osi.Spec.Lemma_9_2_SingleTreeDisjointLeaves := Osi.Headline.lemma_9_2_SingleTreeDisjointLeaves
example : Osi.Spec.Lemma_9_3_TuranCaroWei := Osi.Headline.lemma_9_3_TuranCaroWei
example : Osi.Spec.Lemma_9_4_TuranCenterRows := Osi.Headline.lemma_9_4_TuranCenterRows
example : Osi.Spec.Lemma_9_5_HallMarriage := Osi.Headline.lemma_9_5_HallMarriage
example : Osi.Spec.Lemma_9_6_DisjointLeafReservoirs := Osi.Headline.lemma_9_6_DisjointLeafReservoirs
example : Osi.Spec.Theorem_9_7_WitnessForest := Osi.Headline.theorem_9_7_WitnessForest
example : Osi.Spec.Lemma_10_1_CoordinateSubspaceReduction := Osi.Headline.lemma_10_1_CoordinateSubspaceReduction
example : Osi.Spec.Theorem_10_2_FiniteScale := Osi.Headline.theorem_10_2_FiniteScale
