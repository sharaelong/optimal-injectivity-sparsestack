import Osi.Spec
import Osi.Prelim.SubspaceSing
import Osi.UpperBound.Sec5
import SparseStack.HeadRepair
import SparseStack.Repair.Assembly
import SparseStack.Repair.Retention
import SparseStack.CaseA
import SparseStack.CaseBLinalg

/-!
# Section 6 & Theorem 2.3: Two-Group Heavy-Coordinate Preservation

Proves `Lemma_6_1_SingleGroup`, `Lemma_6_2_TwoGroupIsolation` (at exact `c₁ = 1/1152`),
`Lemma_6_3_TwoGroupHeavy`, and `Theorem_2_3_HeavyPreservation` in full unspecialized generality
(`t₀ ∈ (0, 1/4)`, `δ_rep ∈ (0, 1)`, `H₀ > 0`).
-/

namespace Osi.UpperBound

open Osi.Spec

namespace Sec6Aux

open scoped BigOperators Matrix.Norms.L2Operator

/-! ## 1. Bridges between `Osi.Spec` and `SparseStack` -/

private lemma vecSqNorm_eq_sqNorm {ι : Type} [Fintype ι] (v : ι → ℝ) :
    vecSqNorm v = SparseStack.sqNorm v := by
  simp only [vecSqNorm, SparseStack.sqNorm, dotProduct, sq]

private lemma vecSqNorm_nonneg {ι : Type} [Fintype ι] (v : ι → ℝ) :
    0 ≤ vecSqNorm v := by
  rw [vecSqNorm_eq_sqNorm]
  exact SparseStack.rep_sqNorm_nonneg v

private lemma vecSqNorm_coordVec {n : ℕ} (G : Finset (Fin n)) (v : Fin n → ℝ) :
    vecSqNorm (coordVec G v) = ∑ i ∈ G, v i ^ 2 := by
  rw [vecSqNorm_eq_sqNorm]
  exact SparseStack.sqNorm_restrictVec G v

private lemma uniformProb_eq_sketchLaw_prob {s b n : ℕ} (hb : 0 < b)
    (E : SketchSample s b n → Prop) :
    uniformProb (SketchSample s b n) E = (SparseStack.sketchLaw s b n hb).prob {ω | E ω} :=
  SparseStack.uniformProb_eq_prob hb E

private lemma uniformMeanReal_eq_sketchLaw_expect {s b n : ℕ} (hb : 0 < b)
    (f : SketchSample s b n → ℝ) :
    uniformMeanReal (SketchSample s b n) f = (SparseStack.sketchLaw s b n hb).expect f := by
  rw [uniformMeanReal, SparseStack.sketchLaw_expect_eq_sum hb, div_eq_inv_mul]

private lemma sparseStackOmega_transpose_apply {s b n : ℕ} (ω : SketchSample s b n)
    (j : Fin (s * b)) (i : Fin n) :
    (sparseStackOmega ω).transpose j i =
      SparseStack.sketchMatrix ω (finProdFinEquiv.symm j) i := by
  simp only [Matrix.transpose_apply, sparseStackOmega, SparseStack.sketchMatrix,
    Osi.Spec.signValue, SparseStack.signValue]

private lemma vecSqNorm_sparseStackOmega_mulVec {s b n : ℕ} (ω : SketchSample s b n)
    (v : Fin n → ℝ) :
    vecSqNorm ((sparseStackOmega ω).transpose.mulVec v) =
      SparseStack.sqNorm ((SparseStack.sketchMatrix ω).mulVec v) := by
  rw [vecSqNorm, SparseStack.sqNorm, dotProduct]
  have hmul : ∀ j : Fin (s * b),
      (sparseStackOmega ω).transpose.mulVec v j =
        (SparseStack.sketchMatrix ω).mulVec v (finProdFinEquiv.symm j) := by
    intro j
    simp only [Matrix.mulVec, dotProduct, sparseStackOmega_transpose_apply]
  simp only [hmul, sq]
  exact Equiv.sum_comp finProdFinEquiv.symm
    (fun p => (SparseStack.sketchMatrix ω).mulVec v p *
      (SparseStack.sketchMatrix ω).mulVec v p)

private lemma sparseStackOmega_gram_eq {s b n D : ℕ} (ω : SketchSample s b n)
    (U : Matrix (Fin n) (Fin D) ℝ) :
    ((sparseStackOmega ω).transpose * U).transpose * ((sparseStackOmega ω).transpose * U) =
      (SparseStack.sketchMatrix ω * U).transpose * (SparseStack.sketchMatrix ω * U) := by
  ext k l
  have hmul : ∀ (j : Fin (s * b)) (c : Fin D),
      ((sparseStackOmega ω).transpose * U) j c =
        (SparseStack.sketchMatrix ω * U) (finProdFinEquiv.symm j) c := by
    intro j c
    simp only [Matrix.mul_apply, sparseStackOmega_transpose_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hmul]
  exact Equiv.sum_comp finProdFinEquiv.symm
    (fun p => (SparseStack.sketchMatrix ω * U) p k * (SparseStack.sketchMatrix ω * U) p l)

private lemma retainedCrossGram_eq_crossGram {s b n d : ℕ} (I : Finset (Fin n))
    (V : Matrix (Fin n) (Fin d) ℝ) (ω : SketchSample s b n) :
    retainedCrossGram I V ω = SparseStack.crossGram I V ω := by
  have hTPhi : ∀ (j : Fin (s * b)) (l : Fin n),
      (retainUniqueMatrix I ω * (sparseStackOmega ω).transpose) j l =
        (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω)
          (finProdFinEquiv.symm j) l := by
    intro j l
    rw [retainUniqueMatrix, SparseStack.retainMatrix, Matrix.diagonal_mul,
      Matrix.diagonal_mul, sparseStackOmega_transpose_apply]
    rfl
  have hL : ∀ (j : Fin (s * b)) (i : Fin n),
      (retainUniqueMatrix I ω * (sparseStackOmega ω).transpose *
        Matrix.diagonal (fun i' : Fin n => if i' ∈ I then (1 : ℝ) else 0)) j i =
      (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω *
        SparseStack.coordProj I) (finProdFinEquiv.symm j) i := by
    intro j i
    rw [SparseStack.coordProj, Matrix.mul_diagonal, Matrix.mul_diagonal, hTPhi]
  have hR : ∀ (j : Fin (s * b)) (k : Fin d),
      (retainUniqueMatrix I ω * (sparseStackOmega ω).transpose * V) j k =
      (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω * V)
        (finProdFinEquiv.symm j) k := by
    intro j k
    simp only [Matrix.mul_apply, hTPhi]
  ext i k
  rw [retainedCrossGram, SparseStack.crossGram, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, hL, hR]
  exact Equiv.sum_comp finProdFinEquiv.symm fun p =>
    (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω * SparseStack.coordProj I) p i *
      (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω * V) p k

private lemma spectralNorm_eq_opNorm {m l : Type} [Fintype m] [Fintype l] [DecidableEq l]
    (A : Matrix m l ℝ) :
    spectralNorm A = ‖A‖ := by
  rw [Osi.Spec.spectralNorm, Matrix.l2_opNorm_def]
  rfl

private lemma isolatedBlockCount_eq_retCount {s b n : ℕ} (I : Finset (Fin n))
    (ω : SketchSample s b n) {i : Fin n} (hi : i ∈ I) :
    isolatedBlockCount I ω i = SparseStack.retCount I ω i := by
  unfold isolatedBlockCount SparseStack.retCount
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    SparseStack.bucketLoad_eq_one_iff I ω t hi, SparseStack.aloneIn]
  constructor
  · intro h j hj heq
    by_contra hne
    exact h j hj hne heq
  · intro h j hj hne heq
    exact hne (h j hj heq)

private lemma isolatedBlockCount_mergeHeadSample {s b n : ℕ} (I : Finset (Fin n))
    (ω₀ ω : SketchSample s b n) {i : Fin n} (hi : i ∈ I) :
    isolatedBlockCount I (mergeHeadSample I ω₀ ω) i = isolatedBlockCount I ω₀ i := by
  unfold isolatedBlockCount
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mergeHeadSample, hi, ↓reduceIte]
  constructor
  · intro h j hj hne
    simpa [hj] using h j hj hne
  · intro h j hj hne
    simpa [hj] using h j hj hne

private lemma sdiff_good_eq_badSet {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n) :
    I \ I.filter (fun i => (11 / 12 : ℝ) * (s : ℝ) ≤ (isolatedBlockCount I ω i : ℝ)) =
      SparseStack.badSet I ω := by
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_filter, SparseStack.mem_badSet_iff, SparseStack.a0]
  constructor
  · rintro ⟨hi, hnot⟩
    refine ⟨hi, ?_⟩
    have hnot' : ¬ (11 / 12 : ℝ) * (s : ℝ) ≤ (isolatedBlockCount I ω i : ℝ) :=
      fun h => hnot ⟨hi, h⟩
    rw [← isolatedBlockCount_eq_retCount I ω hi]
    exact not_le.mp hnot'
  · rintro ⟨hi, hlt⟩
    refine ⟨hi, fun ⟨_, hge⟩ => ?_⟩
    rw [isolatedBlockCount_eq_retCount I ω hi] at hge
    exact not_lt_of_ge hge hlt

private lemma prob_of_cond_mergeHead {s b n : ℕ} (hb : 0 < b) (I : Finset (Fin n))
    (P : SketchSample s b n → Prop) {c : ℝ}
    (hc : ∀ ω₀ : SketchSample s b n,
      c ≤ (SparseStack.sketchLaw s b n hb).prob {ω | P (mergeHeadSample I ω₀ ω)}) :
    c ≤ (SparseStack.sketchLaw s b n hb).prob {ω | P ω} := by
  rw [SparseFock.FiniteLaw.prob, SparseStack.expect_mergeHead hb I]
  calc c = (SparseStack.sketchLaw s b n hb).expect (fun _ => c) :=
        (SparseFock.FiniteLaw.expect_const _ c).symm
    _ ≤ (SparseStack.sketchLaw s b n hb).expect (fun ω₀ =>
          (SparseStack.sketchLaw s b n hb).expect
            (fun ω => SparseFock.FiniteLaw.indicator {ω' | P ω'}
              (SparseStack.mergeHead I ω₀ ω))) := by
        apply SparseFock.FiniteLaw.expect_mono
        intro ω₀
        refine (hc ω₀).trans_eq ?_
        rw [SparseFock.FiniteLaw.prob]
        apply SparseFock.FiniteLaw.expect_congr
        intro ω
        have hm : mergeHeadSample I ω₀ ω = SparseStack.mergeHead I ω₀ ω := rfl
        by_cases hP : P (mergeHeadSample I ω₀ ω)
        · rw [SparseStack.indicator_of_mem (show ω ∈ {ω | P (mergeHeadSample I ω₀ ω)} from hP),
            ← hm, SparseStack.indicator_of_mem (show mergeHeadSample I ω₀ ω ∈ {ω' | P ω'} from hP)]
        · rw [SparseStack.indicator_of_notMem (show ω ∉ {ω | P (mergeHeadSample I ω₀ ω)} from hP),
            ← hm,
            SparseStack.indicator_of_notMem (show mergeHeadSample I ω₀ ω ∉ {ω' | P ω'} from hP)]

/-! ## 2. Helpers for Lemma 6.1 (Single-Group Certificate & Cross-Term Probability) -/

private lemma cert_core_gen {s b n d : ℕ} (I : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ)
    (ω : SketchSample s b n) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hM : ‖SparseStack.crossGram I V ω‖ ≤ t₀)
    (h : Fin n → ℝ) (hh : ∀ i : Fin n, i ∉ I → h i = 0) (f : Fin d → ℝ) :
    SparseStack.sqNorm ((SparseStack.retainMatrix I ω).mulVec
        ((SparseStack.sketchMatrix ω).mulVec h)) - t₀ * SparseStack.sqNorm h ≤
      SparseStack.sqNorm ((SparseStack.sketchMatrix ω).mulVec (h + V.mulVec f)) +
        t₀ * SparseStack.sqNorm f := by
  have hPh : (SparseStack.coordProj I).mulVec h = h := by
    funext i
    rw [SparseStack.coordProj, Matrix.mulVec_diagonal]
    by_cases hi : i ∈ I
    · simp [hi]
    · simp [hi, hh i hi]
  have hA : (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω *
        SparseStack.coordProj I).mulVec h =
      (SparseStack.retainMatrix I ω).mulVec ((SparseStack.sketchMatrix ω).mulVec h) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPh]
  have hC : (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω * V).mulVec f =
      (SparseStack.retainMatrix I ω).mulVec ((SparseStack.sketchMatrix ω).mulVec (V.mulVec f)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hinner : dotProduct
      ((SparseStack.retainMatrix I ω).mulVec ((SparseStack.sketchMatrix ω).mulVec h))
      ((SparseStack.retainMatrix I ω).mulVec ((SparseStack.sketchMatrix ω).mulVec (V.mulVec f))) =
      dotProduct h ((SparseStack.crossGram I V ω).mulVec f) := by
    have e1 : (SparseStack.crossGram I V ω).mulVec f =
        (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω *
          SparseStack.coordProj I).transpose.mulVec
          ((SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω * V).mulVec f) := by
      rw [SparseStack.crossGram, Matrix.mulVec_mulVec]
    rw [e1, Matrix.dotProduct_mulVec h, Matrix.vecMul_transpose, hA, hC]
  have hsplit : (SparseStack.retainMatrix I ω).mulVec
      ((SparseStack.sketchMatrix ω).mulVec (h + V.mulVec f)) =
      (SparseStack.retainMatrix I ω).mulVec ((SparseStack.sketchMatrix ω).mulVec h) +
        (SparseStack.retainMatrix I ω).mulVec
          ((SparseStack.sketchMatrix ω).mulVec (V.mulVec f)) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add]
  have hdel := SparseStack.sqNorm_retain_mulVec_le I ω
    ((SparseStack.sketchMatrix ω).mulVec (h + V.mulVec f))
  rw [hsplit] at hdel
  have hMf : SparseStack.sqNorm ((SparseStack.crossGram I V ω).mulVec f) ≤
      t₀ ^ 2 * SparseStack.sqNorm f := by
    have h1 := SparseStack.sqNorm_mulVec_le_opNorm (SparseStack.crossGram I V ω) f
    have h2 : ‖SparseStack.crossGram I V ω‖ ^ 2 ≤ t₀ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hM 2
    have h3 := SparseStack.rep_sqNorm_nonneg f
    nlinarith
  have hCS := SparseStack.rep_dot_sq_le h ((SparseStack.crossGram I V ω).mulVec f)
  rw [← hinner] at hCS
  generalize (SparseStack.retainMatrix I ω).mulVec ((SparseStack.sketchMatrix ω).mulVec h) = a
    at hdel hCS ⊢
  generalize (SparseStack.retainMatrix I ω).mulVec
    ((SparseStack.sketchMatrix ω).mulVec (V.mulVec f)) = c at hdel hCS
  generalize SparseStack.sqNorm ((SparseStack.crossGram I V ω).mulVec f) = X at hMf hCS
  have hH := SparseStack.rep_sqNorm_nonneg h
  have hF := SparseStack.rep_sqNorm_nonneg f
  have hz2 : (2 * dotProduct a c) ^ 2 ≤ (t₀ * (SparseStack.sqNorm h + SparseStack.sqNorm f)) ^ 2 := by
    have k1 := mul_le_mul_of_nonneg_left hMf hH
    have k2 : 0 ≤ t₀ ^ 2 * (SparseStack.sqNorm h - SparseStack.sqNorm f) ^ 2 := by positivity
    nlinarith
  have hcross : -(t₀ * (SparseStack.sqNorm h + SparseStack.sqNorm f)) ≤ 2 * dotProduct a c :=
    (abs_le_of_sq_le_sq' hz2 (by positivity)).1
  have hexp : SparseStack.sqNorm (a + c) =
      SparseStack.sqNorm a + 2 * dotProduct a c + SparseStack.sqNorm c := by
    unfold SparseStack.sqNorm
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm c a]
    ring
  rw [hexp] at hdel
  have hc0 := SparseStack.rep_sqNorm_nonneg c
  linarith

private lemma single_group_cert {ζ₀ b n d₀ : ℕ} (hζ₀ : 0 < ζ₀)
    (I₀ : Finset (Fin n)) (V₀ : Matrix (Fin n) (Fin d₀) ℝ)
    (ω₀ ω : SketchSample ζ₀ b n) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hM : spectralNorm (retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω)) ≤ t₀)
    (h : Fin n → ℝ) (f : Fin d₀ → ℝ) (hh : ∀ i : Fin n, i ∉ I₀ → h i = 0) :
    let G₀ := I₀.filter (fun i => (11 / 12 : ℝ) * (ζ₀ : ℝ) ≤ (isolatedBlockCount I₀ ω₀ i : ℝ))
    let B₀ := I₀ \ G₀
    (11 / 12 - t₀) * vecSqNorm (coordVec G₀ h) - t₀ * vecSqNorm (coordVec B₀ h) ≤
      vecSqNorm ((sparseStackOmega (mergeHeadSample I₀ ω₀ ω)).transpose.mulVec
        (h + V₀.mulVec f)) + t₀ * vecSqNorm f := by
  intro G₀ B₀
  have hζ₀' : (0 : ℝ) < ζ₀ := Nat.cast_pos.2 hζ₀
  set ω' := mergeHeadSample I₀ ω₀ ω
  have hM' : ‖SparseStack.crossGram I₀ V₀ ω'‖ ≤ t₀ := by
    rwa [← spectralNorm_eq_opNorm, ← retainedCrossGram_eq_crossGram]
  have core := cert_core_gen I₀ V₀ ω' ht₀ hM' h hh f
  have gram := SparseStack.retained_head_gram I₀ ω' h hh
  rw [← Matrix.mulVec_mulVec] at gram
  rw [gram] at core
  have hdisj : Disjoint G₀ B₀ := Finset.disjoint_sdiff
  have hunion : G₀ ∪ B₀ = I₀ := Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
  have hsplit_gram : ∑ i ∈ I₀, (SparseStack.retCount I₀ ω' i : ℝ) / ζ₀ * h i ^ 2 =
      (∑ i ∈ G₀, (SparseStack.retCount I₀ ω' i : ℝ) / ζ₀ * h i ^ 2) +
        (∑ i ∈ B₀, (SparseStack.retCount I₀ ω' i : ℝ) / ζ₀ * h i ^ 2) := by
    rw [← hunion, Finset.sum_union hdisj]
  have hbad_nn : 0 ≤ ∑ i ∈ B₀, (SparseStack.retCount I₀ ω' i : ℝ) / ζ₀ * h i ^ 2 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hgood_ge : (11 / 12 : ℝ) * ∑ i ∈ G₀, h i ^ 2 ≤
      ∑ i ∈ G₀, (SparseStack.retCount I₀ ω' i : ℝ) / ζ₀ * h i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hiI : i ∈ I₀ := (Finset.mem_filter.1 hi).1
    have hge : (11 / 12 : ℝ) * (ζ₀ : ℝ) ≤ (isolatedBlockCount I₀ ω₀ i : ℝ) :=
      (Finset.mem_filter.1 hi).2
    have hret_eq : SparseStack.retCount I₀ ω' i = isolatedBlockCount I₀ ω₀ i := by
      rw [← isolatedBlockCount_eq_retCount I₀ ω' hiI,
        isolatedBlockCount_mergeHeadSample I₀ ω₀ ω hiI]
    have ha : (11 / 12 : ℝ) ≤ (SparseStack.retCount I₀ ω' i : ℝ) / ζ₀ := by
      rw [le_div_iff₀ hζ₀', hret_eq]
      exact hge
    exact mul_le_mul_of_nonneg_right ha (sq_nonneg _)
  have hnorm_split : SparseStack.sqNorm h =
      vecSqNorm (coordVec G₀ h) + vecSqNorm (coordVec B₀ h) := by
    have h1 : SparseStack.sqNorm h = ∑ i ∈ I₀, h i ^ 2 := by
      unfold SparseStack.sqNorm dotProduct
      rw [Finset.sum_subset (Finset.subset_univ I₀) (fun i _ hi => by simp [hh i hi])]
      simp only [sq]
    rw [h1, ← hunion, Finset.sum_union hdisj, vecSqNorm_coordVec, vecSqNorm_coordVec]
  rw [vecSqNorm_sparseStackOmega_mulVec, vecSqNorm_eq_sqNorm f]
  rw [hnorm_split, hsplit_gram] at core
  rw [← vecSqNorm_coordVec G₀ h] at hgood_ge
  linarith

private lemma logER_pow_four_le {R : ℝ} (hR : 1 ≤ R) :
    Real.log (Real.exp 1 * R) ^ 4 ≤ 192 * R := by
  have hR0 : 0 < R := by linarith
  have hRe := SparseStack.repnum_R_eq_exp hR0
  have hL1 : 1 ≤ Real.log (Real.exp 1 * R) := by
    rw [SparseStack.repnum_logER_eq hR0]
    linarith [Real.log_nonneg hR]
  set L := Real.log (Real.exp 1 * R)
  set x := L - 1
  have hx : 0 ≤ x := by linarith
  have h5 := Real.sum_le_exp_of_nonneg hx 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h5
  norm_num [Nat.factorial] at h5
  have hexp : 1 + x ^ 4 / 24 ≤ R := by
    rw [hRe]
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx 3
    linarith
  have h1 : (x + 1) ^ 2 ≤ 2 * (x ^ 2 + 1) := by nlinarith [sq_nonneg (x - 1)]
  have h2 : (x + 1) ^ 4 ≤ 4 * (x ^ 2 + 1) ^ 2 := by
    calc (x + 1) ^ 4 = ((x + 1) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (x ^ 2 + 1)) ^ 2 := pow_le_pow_left₀ (sq_nonneg (x + 1)) h1 2
      _ = 4 * (x ^ 2 + 1) ^ 2 := by ring
  have h3 : (x ^ 2 + 1) ^ 2 ≤ 2 * (x ^ 4 + 1) := by nlinarith [sq_nonneg (x ^ 2 - 1)]
  have hLx : L = x + 1 := by ring
  rw [hLx]
  linarith

private lemma cross_rhs_le_target {R ζ₀ b N d₀ p : ℕ} {C_cg H₀ δ_target C₀ K₀ : ℝ}
    (hR : 2 ≤ R) (hC_cg : 0 < C_cg) (hH₀ : 0 < H₀) (hδ_target : 0 < δ_target)
    (hC₀_def : C₀ = 2 + 4 / δ_target)
    (hK₀_def : K₀ = 1 + 22 / δ_target ^ 2 + 64 * H₀ ^ 4 / δ_target ^ 2)
    (hζ_lo : C₀ * Real.sqrt (Real.log (Real.exp 1 * (R : ℝ))) ≤ (ζ₀ : ℝ))
    (hζ_hi : (ζ₀ : ℝ) ≤ H₀ * Real.log (Real.exp 1 * (R : ℝ)))
    (hk : K₀ * (R : ℝ) ≤ ((ζ₀ * b : ℕ) : ℝ))
    (hbs : 2 * ζ₀ ≤ b) (hd₀ : d₀ ≤ 2 * R) (hN : N ≤ R)
    (hp_def : p = ⌈Real.log (2 * Real.exp 1 * (R : ℝ))⌉₊) :
    C_cg * (Real.sqrt (((N : ℝ) + ((d₀ : ℝ) + 2 * (p : ℝ) + 1)) / ((ζ₀ * b : ℕ) : ℝ) +
        ((p : ℝ) + 1) / (ζ₀ : ℝ) ^ 2) +
      Real.sqrt ((N : ℝ) * (d₀ : ℝ) / ((ζ₀ : ℝ) ^ 2 * (b : ℝ) ^ 3) *
        (Nat.choose ζ₀ 3 : ℝ))) ≤
      C_cg * (2 * δ_target) := by
  set L := Real.log (Real.exp 1 * (R : ℝ))
  have hR1 : (1 : ℝ) ≤ R := by
    have : (2 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hL1 : 1 ≤ L := SparseStack.one_le_logER (by omega)
  have hL_le_R : L ≤ R := SparseStack.logER_le (by omega)
  have hL4 : L ^ 4 ≤ 192 * R := logER_pow_four_le hR1
  have hsqrtL1 : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL1
  have hC₀_gt2 : 2 < C₀ := by
    rw [hC₀_def]
    have : 0 < 4 / δ_target := by positivity
    linarith
  have hζ₀_gt2 : (2 : ℝ) < ζ₀ := by nlinarith
  have hζ₀_pos : (0 : ℝ) < ζ₀ := by linarith
  have hb_pos : (0 : ℝ) < b := by
    have : (4 : ℝ) < b := by
      have hbsR : (2 * ζ₀ : ℝ) ≤ b := by exact_mod_cast hbs
      linarith
    linarith
  have hK₀_gt1 : 1 < K₀ := by
    rw [hK₀_def]
    have : 0 < 22 / δ_target ^ 2 + 64 * H₀ ^ 4 / δ_target ^ 2 := by positivity
    linarith
  have hK₀_pos : 0 < K₀ := by linarith
  have hzb_pos : 0 < ((ζ₀ * b : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hk
  -- Bound on `p + 1 ≤ 4 L` and `N + d₀ + 2p + 1 ≤ 11 R`
  have hp_le : (p : ℝ) + 1 ≤ 4 * L := by
    have hlog_eq : Real.log (2 * Real.exp 1 * (R : ℝ)) = Real.log 2 + L :=
      SparseStack.repnum_log2eR_eq hR0
    have hl2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl2_lt := Real.log_two_lt_d9
    norm_num at hl2_lt
    have hnn : 0 ≤ Real.log (2 * Real.exp 1 * (R : ℝ)) := by linarith
    have hc : (p : ℝ) < Real.log (2 * Real.exp 1 * (R : ℝ)) + 1 := by
      rw [hp_def]
      exact Nat.ceil_lt_add_one hnn
    linarith
  have hND_le : (N : ℝ) + ((d₀ : ℝ) + 2 * (p : ℝ) + 1) ≤ 11 * R := by
    have hNR : (N : ℝ) ≤ R := by exact_mod_cast hN
    have hdR : (d₀ : ℝ) ≤ 2 * R := by exact_mod_cast hd₀
    linarith
  -- First square root `≤ δ_target`
  have hterm1a : ((N : ℝ) + ((d₀ : ℝ) + 2 * (p : ℝ) + 1)) / ((ζ₀ * b : ℕ) : ℝ) ≤
      δ_target ^ 2 / 2 := by
    rw [div_le_div_iff₀ hzb_pos (by norm_num)]
    have hk_ge : 22 / δ_target ^ 2 ≤ K₀ := by
      rw [hK₀_def]
      have : 0 ≤ 64 * H₀ ^ 4 / δ_target ^ 2 := by positivity
      linarith
    have h22 : (22 : ℝ) ≤ K₀ * δ_target ^ 2 := by
      have := mul_le_mul_of_nonneg_right hk_ge (sq_nonneg δ_target)
      have hne : δ_target ^ 2 ≠ 0 := pow_ne_zero 2 hδ_target.ne'
      rwa [div_mul_cancel₀ _ hne] at this
    calc ((N : ℝ) + ((d₀ : ℝ) + 2 * (p : ℝ) + 1)) * 2 ≤ 22 * R := by linarith
      _ ≤ (K₀ * δ_target ^ 2) * R := mul_le_mul_of_nonneg_right h22 hR0.le
      _ = δ_target ^ 2 * (K₀ * R) := by ring
      _ ≤ δ_target ^ 2 * ((ζ₀ * b : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hk (sq_nonneg δ_target)
  have hterm1b : ((p : ℝ) + 1) / (ζ₀ : ℝ) ^ 2 ≤ δ_target ^ 2 / 2 := by
    rw [div_le_div_iff₀ (pow_pos hζ₀_pos 2) (by norm_num)]
    have hζ2 : C₀ ^ 2 * L ≤ (ζ₀ : ℝ) ^ 2 := by
      have h1 := pow_le_pow_left₀ (by positivity) hζ_lo 2
      rw [mul_pow, Real.sq_sqrt (by linarith)] at h1
      exact h1
    have hC_ge : 4 / δ_target ≤ C₀ := by
      rw [hC₀_def]
      linarith
    have hCδ : (4 : ℝ) ≤ C₀ * δ_target := by
      have := mul_le_mul_of_nonneg_right hC_ge hδ_target.le
      rwa [div_mul_cancel₀ _ hδ_target.ne'] at this
    have hC2δ : (16 : ℝ) ≤ C₀ ^ 2 * δ_target ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) hCδ 2
      linarith
    calc ((p : ℝ) + 1) * 2 ≤ 8 * L := by linarith
      _ ≤ 16 * L := by linarith
      _ ≤ (C₀ ^ 2 * δ_target ^ 2) * L := mul_le_mul_of_nonneg_right hC2δ (by linarith)
      _ = δ_target ^ 2 * (C₀ ^ 2 * L) := by ring
      _ ≤ δ_target ^ 2 * (ζ₀ : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hζ2 (sq_nonneg δ_target)
  have hsqrt1 : Real.sqrt (((N : ℝ) + ((d₀ : ℝ) + 2 * (p : ℝ) + 1)) / ((ζ₀ * b : ℕ) : ℝ) +
      ((p : ℝ) + 1) / (ζ₀ : ℝ) ^ 2) ≤ δ_target := by
    calc Real.sqrt (((N : ℝ) + ((d₀ : ℝ) + 2 * (p : ℝ) + 1)) / ((ζ₀ * b : ℕ) : ℝ) +
          ((p : ℝ) + 1) / (ζ₀ : ℝ) ^ 2)
        ≤ Real.sqrt (δ_target ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = δ_target := Real.sqrt_sq hδ_target.le
  -- Second square root `≤ δ_target`
  have hc3 : (Nat.choose ζ₀ 3 : ℝ) ≤ (ζ₀ : ℝ) ^ 3 / 6 := by
    have h := Nat.choose_le_pow_div (α := ℝ) 3 ζ₀
    norm_num [Nat.factorial] at h
    exact h
  have hNd_le : (N : ℝ) * (d₀ : ℝ) ≤ 2 * (R : ℝ) ^ 2 := by
    have hNR : (N : ℝ) ≤ R := by exact_mod_cast hN
    have hdR : (d₀ : ℝ) ≤ 2 * R := by exact_mod_cast hd₀
    have := mul_le_mul hNR hdR (Nat.cast_nonneg d₀) hR0.le
    linarith
  have hrem_step1 : (N : ℝ) * (d₀ : ℝ) / ((ζ₀ : ℝ) ^ 2 * (b : ℝ) ^ 3) * (Nat.choose ζ₀ 3 : ℝ) ≤
      (R : ℝ) ^ 2 * (ζ₀ : ℝ) ^ 4 / (3 * ((ζ₀ : ℝ) * (b : ℝ)) ^ 3) := by
    calc (N : ℝ) * (d₀ : ℝ) / ((ζ₀ : ℝ) ^ 2 * (b : ℝ) ^ 3) * (Nat.choose ζ₀ 3 : ℝ)
        ≤ (2 * (R : ℝ) ^ 2) / ((ζ₀ : ℝ) ^ 2 * (b : ℝ) ^ 3) * ((ζ₀ : ℝ) ^ 3 / 6) := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_right hNd_le (by positivity)
          · exact hc3
          · positivity
          · positivity
      _ = (R : ℝ) ^ 2 * (ζ₀ : ℝ) ^ 4 / (3 * ((ζ₀ : ℝ) * (b : ℝ)) ^ 3) := by
          field_simp
          ring
  have hrem_step2 : (R : ℝ) ^ 2 * (ζ₀ : ℝ) ^ 4 / (3 * ((ζ₀ : ℝ) * (b : ℝ)) ^ 3) ≤
      δ_target ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hζ4 : (ζ₀ : ℝ) ^ 4 ≤ 192 * H₀ ^ 4 * R := by
      calc (ζ₀ : ℝ) ^ 4 ≤ (H₀ * L) ^ 4 := pow_le_pow_left₀ hζ₀_pos.le hζ_hi 4
        _ = H₀ ^ 4 * L ^ 4 := by ring
        _ ≤ H₀ ^ 4 * (192 * R) := mul_le_mul_of_nonneg_left hL4 (by positivity)
        _ = 192 * H₀ ^ 4 * R := by ring
    have hnum : (R : ℝ) ^ 2 * (ζ₀ : ℝ) ^ 4 ≤ 192 * H₀ ^ 4 * (R : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_left hζ4 (sq_nonneg (R : ℝ))
      linarith
    have hzb_ge : K₀ * (R : ℝ) ≤ (ζ₀ : ℝ) * (b : ℝ) := by
      simpa [Nat.cast_mul] using hk
    have hden : K₀ ^ 3 * (R : ℝ) ^ 3 ≤ ((ζ₀ : ℝ) * (b : ℝ)) ^ 3 := by
      calc K₀ ^ 3 * (R : ℝ) ^ 3 = (K₀ * R) ^ 3 := by ring
        _ ≤ ((ζ₀ : ℝ) * (b : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hzb_ge 3
    have hK_pow : K₀ ≤ K₀ ^ 3 := by
      nlinarith [sq_nonneg (K₀ - 1)]
    have hk_rem : 64 * H₀ ^ 4 / δ_target ^ 2 ≤ K₀ := by
      rw [hK₀_def]
      have : 0 ≤ 22 / δ_target ^ 2 := by positivity
      linarith
    have h64 : 64 * H₀ ^ 4 ≤ δ_target ^ 2 * K₀ := by
      have := mul_le_mul_of_nonneg_right hk_rem (sq_nonneg δ_target)
      have hne : δ_target ^ 2 ≠ 0 := pow_ne_zero 2 hδ_target.ne'
      linarith [div_mul_cancel₀ (64 * H₀ ^ 4) hne]
    calc (R : ℝ) ^ 2 * (ζ₀ : ℝ) ^ 4 ≤ 192 * H₀ ^ 4 * (R : ℝ) ^ 3 := hnum
      _ = 3 * (64 * H₀ ^ 4) * (R : ℝ) ^ 3 := by ring
      _ ≤ 3 * (δ_target ^ 2 * K₀) * (R : ℝ) ^ 3 := by gcongr
      _ ≤ 3 * (δ_target ^ 2 * K₀ ^ 3) * (R : ℝ) ^ 3 := by gcongr
      _ = δ_target ^ 2 * (3 * (K₀ ^ 3 * (R : ℝ) ^ 3)) := by ring
      _ ≤ δ_target ^ 2 * (3 * ((ζ₀ : ℝ) * (b : ℝ)) ^ 3) := by gcongr
  have hsqrt2 : Real.sqrt ((N : ℝ) * (d₀ : ℝ) / ((ζ₀ : ℝ) ^ 2 * (b : ℝ) ^ 3) *
      (Nat.choose ζ₀ 3 : ℝ)) ≤ δ_target := by
    calc Real.sqrt ((N : ℝ) * (d₀ : ℝ) / ((ζ₀ : ℝ) ^ 2 * (b : ℝ) ^ 3) *
          (Nat.choose ζ₀ 3 : ℝ))
        ≤ Real.sqrt (δ_target ^ 2) := Real.sqrt_le_sqrt (hrem_step1.trans hrem_step2)
      _ = δ_target := Real.sqrt_sq hδ_target.le
  exact mul_le_mul_of_nonneg_left (by linarith) hC_cg.le

/-! ## 3. Helpers for Lemma 6.2 (Exact `c₁ = 1/1152` Isolation via `5/4`-Base MGF) -/

private lemma log_65_64_sub_log_5_4_div_12_le :
    Real.log (65 / 64 : ℝ) - Real.log (5 / 4 : ℝ) / 12 ≤ -(1 / 576 : ℝ) := by
  have h65 : Real.log (65 / 64 : ℝ) ≤ 1 / 64 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 65 / 64)
    linarith
  have h54 : (5 / 24 : ℝ) ≤ Real.log (5 / 4 : ℝ) := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 5 / 4)]
    have he1 : (43 / 48 : ℝ) ≤ Real.exp (-(5 / 48 : ℝ)) := by
      have h := Real.add_one_le_exp (-(5 / 48 : ℝ))
      linarith
    have he2 : (43 / 48 : ℝ) ^ 2 ≤ Real.exp (-(5 / 24 : ℝ)) := by
      calc (43 / 48 : ℝ) ^ 2 ≤ Real.exp (-(5 / 48 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by norm_num) he1 2
        _ = Real.exp (-(5 / 24 : ℝ)) := by
            rw [sq, ← Real.exp_add]
            norm_num
    have hprod : Real.exp (-(5 / 24 : ℝ)) * Real.exp (5 / 24 : ℝ) = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hexp_pos : 0 < Real.exp (5 / 24 : ℝ) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right he2 hexp_pos.le
    rw [hprod] at hmul
    norm_num at hmul
    linarith
  linarith

private lemma prod_ite_const_one {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p]
    (c : ℝ) :
    (∏ x ∈ s, if p x then c else 1) = c ^ (s.filter p).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.filter_insert]
    split_ifs with hpa
    · rw [Finset.card_insert_of_notMem (by simp [ha]), pow_succ', ih]
    · rw [one_mul, ih]

/-- Sharp single-coordinate lower tail via independent-block `5/4`-base MGF:
`P(retCount I ω i < (11/12) s) ≤ exp(-s / 576)` whenever `16 |I| ≤ b` and `i ∈ I`. -/
private lemma prob_retCount_lt_le_sharp {s b n : ℕ} (hb : 0 < b) (I : Finset (Fin n))
    (hIb : 16 * I.card ≤ b) {i : Fin n} (hi : i ∈ I) :
    (SparseStack.sketchLaw s b n hb).prob
        {ω | (SparseStack.retCount I ω i : ℝ) < SparseStack.a0 * s} ≤
      Real.exp (-(s : ℝ) / 576) := by
  classical
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  rw [SparseStack.sketchLaw_prob_ofBlocks hb]
  set μ : Fin s → SparseFock.FiniteLaw (SparseStack.BlockSample b n) :=
    fun _ => SparseStack.blockLaw b n hb
  set g : SparseStack.BlockSample b n → ℝ :=
    fun y => if ¬ SparseStack.aloneIn I i y then (5 / 4 : ℝ) else 1
  set M : (Fin s → SparseStack.BlockSample b n) → ℝ := fun x => ∏ t : Fin s, g (x t)
  have hg_nn : ∀ y : SparseStack.BlockSample b n, 0 ≤ g y := by
    intro y
    simp only [g]
    split_ifs <;> norm_num
  have hM_nn : ∀ x : Fin s → SparseStack.BlockSample b n, 0 ≤ M x :=
    fun x => Finset.prod_nonneg (fun t _ => hg_nn (x t))
  have hg_eq : ∀ y : SparseStack.BlockSample b n,
      g y = 1 + (1 / 4 : ℝ) *
        SparseFock.FiniteLaw.indicator {y | ¬ SparseStack.aloneIn I i y} y := by
    intro y
    by_cases hy : ¬ SparseStack.aloneIn I i y
    · rw [SparseStack.indicator_of_mem (show y ∈ {y | ¬ SparseStack.aloneIn I i y} from hy)]
      simp only [g, if_pos hy]
      norm_num
    · rw [SparseStack.indicator_of_notMem (show y ∉ {y | ¬ SparseStack.aloneIn I i y} from hy)]
      simp only [g, if_neg hy]
      norm_num
  have hEg_nn : 0 ≤ (SparseStack.blockLaw b n hb).expect g :=
    SparseFock.FiniteLaw.expect_nonneg _ hg_nn
  have hEg_le : (SparseStack.blockLaw b n hb).expect g ≤ 65 / 64 := by
    rw [SparseFock.FiniteLaw.expect_congr _ hg_eq, SparseFock.FiniteLaw.expect_add,
      SparseFock.FiniteLaw.expect_const, SparseFock.FiniteLaw.expect_smul]
    have hprob_eq : (SparseStack.blockLaw b n hb).expect
        (SparseFock.FiniteLaw.indicator {y | ¬ SparseStack.aloneIn I i y}) =
        (SparseStack.blockLaw b n hb).prob {y | ¬ SparseStack.aloneIn I i y} := rfl
    rw [hprob_eq]
    have h1 := SparseStack.blockLaw_prob_not_alone_le hb I i
    have h2 : (I.card : ℝ) / b ≤ 1 / 16 := by
      rw [div_le_iff₀ hb']
      have : (16 * I.card : ℝ) ≤ b := by exact_mod_cast hIb
      linarith
    linarith
  have hS : Pairwise (fun j k : Fin s => Disjoint ({j} : Finset (Fin s)) {k}) :=
    fun _ _ hjk => Finset.disjoint_singleton.2 hjk
  have hEM : (SparseFock.FiniteLaw.independentProduct μ).expect M ≤
      Real.exp ((s : ℝ) * Real.log (65 / 64 : ℝ)) := by
    have hfact : (SparseFock.FiniteLaw.independentProduct μ).expect M =
        ((SparseStack.blockLaw b n hb).expect g) ^ s := by
      rw [SparseStack.expect_prod_disjoint_blocks μ (fun t : Fin s => ({t} : Finset (Fin s)))
        hS (fun t x => g (x t))]
      · have h1 : ∀ t : Fin s,
            (SparseFock.FiniteLaw.independentProduct μ).expect (fun x => g (x t)) =
              (SparseStack.blockLaw b n hb).expect g :=
          fun t => SparseFock.FiniteLaw.expect_independentProduct_apply μ t g
        rw [Finset.prod_congr rfl (fun t _ => h1 t), Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
      · intro t x y hxy
        rw [hxy t (Finset.mem_singleton_self t)]
    calc (SparseFock.FiniteLaw.independentProduct μ).expect M
        = ((SparseStack.blockLaw b n hb).expect g) ^ s := hfact
      _ ≤ (65 / 64 : ℝ) ^ s := pow_le_pow_left₀ hEg_nn hEg_le s
      _ = Real.exp ((s : ℝ) * Real.log (65 / 64 : ℝ)) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  set thr := Real.exp ((s : ℝ) * (Real.log (5 / 4 : ℝ) / 12))
  have hthr_pos : 0 < thr := Real.exp_pos _
  have hsub : {x : Fin s → SparseStack.BlockSample b n |
      (SparseStack.retCount I (SparseStack.ofBlocks x) i : ℝ) < SparseStack.a0 * s} ⊆
      {x | thr ≤ M x} := by
    intro x hx
    have hx' : (SparseStack.retCount I (SparseStack.ofBlocks x) i : ℝ) < SparseStack.a0 * s := hx
    have hret_eq : SparseStack.retCount I (SparseStack.ofBlocks x) i =
        (Finset.univ.filter (fun t : Fin s => SparseStack.aloneIn I i (x t))).card := by
      unfold SparseStack.retCount
      congr 1
      apply Finset.filter_congr
      intro t _
      exact SparseStack.bucketLoad_eq_one_iff I (SparseStack.ofBlocks x) t hi
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin s)))
      (fun t : Fin s => SparseStack.aloneIn I i (x t))
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    set k := (Finset.univ.filter (fun t : Fin s => ¬ SparseStack.aloneIn I i (x t))).card
    have hsumR : (SparseStack.retCount I (SparseStack.ofBlocks x) i : ℝ) + (k : ℝ) = (s : ℝ) := by
      rw [hret_eq]
      exact_mod_cast hsplit
    have hk_ge : (s : ℝ) / 12 ≤ (k : ℝ) := by
      simp only [SparseStack.a0] at hx'
      linarith
    have hMx : M x = Real.exp ((k : ℝ) * Real.log (5 / 4 : ℝ)) := by
      have hprod := prod_ite_const_one (Finset.univ : Finset (Fin s))
        (fun t : Fin s => ¬ SparseStack.aloneIn I i (x t)) (5 / 4 : ℝ)
      calc M x = (5 / 4 : ℝ) ^ k := hprod
        _ = Real.exp ((k : ℝ) * Real.log (5 / 4 : ℝ)) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    show thr ≤ M x
    rw [hMx]
    apply Real.exp_le_exp.mpr
    have hlog54_pos : 0 < Real.log (5 / 4 : ℝ) := Real.log_pos (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hk_ge hlog54_pos.le
    linarith
  calc (SparseFock.FiniteLaw.independentProduct μ).prob
        {x | (SparseStack.retCount I (SparseStack.ofBlocks x) i : ℝ) < SparseStack.a0 * s}
      ≤ (SparseFock.FiniteLaw.independentProduct μ).prob {x | thr ≤ M x} :=
        SparseFock.FiniteLaw.prob_mono _ hsub
    _ ≤ (SparseFock.FiniteLaw.independentProduct μ).expect M / thr :=
        SparseFock.FiniteLaw.markov _ hM_nn hthr_pos
    _ ≤ Real.exp ((s : ℝ) * Real.log (65 / 64 : ℝ)) / thr :=
        div_le_div_of_nonneg_right hEM hthr_pos.le
    _ = Real.exp ((s : ℝ) * (Real.log (65 / 64 : ℝ) - Real.log (5 / 4 : ℝ) / 12)) := by
        rw [← Real.exp_sub]
        congr 1
        ring
    _ ≤ Real.exp (-(s : ℝ) / 576) := by
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_left log_65_64_sub_log_5_4_div_12_le (Nat.cast_nonneg s)
        linarith

/-- Sharp Markov bound on `badSet`: `P(|B| > N exp(-s / 1152)) ≤ exp(-s / 1152)`. -/
private lemma prob_badSet_card_le_sharp {s b n : ℕ} (hb : 0 < b) (I : Finset (Fin n))
    (hIb : 16 * I.card ≤ b) :
    (SparseStack.sketchLaw s b n hb).prob
        {ω | (I.card : ℝ) * Real.exp (-(s : ℝ) / 1152) < (SparseStack.badSet I ω).card} ≤
      Real.exp (-(s : ℝ) / 1152) := by
  classical
  have hsq : Real.exp (-(s : ℝ) / 576) =
      Real.exp (-(s : ℝ) / 1152) * Real.exp (-(s : ℝ) / 1152) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he : 0 < Real.exp (-(s : ℝ) / 1152) := Real.exp_pos _
  have hcard : ∀ ω : SketchSample s b n, ((SparseStack.badSet I ω).card : ℝ) =
      ∑ j ∈ I, SparseFock.FiniteLaw.indicator
        {ω | (SparseStack.retCount I ω j : ℝ) < SparseStack.a0 * s} ω := by
    intro ω
    rw [SparseStack.badSet, Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : (SparseStack.retCount I ω j : ℝ) < SparseStack.a0 * s
    · rw [if_pos h, SparseStack.indicator_of_mem
        (show ω ∈ {ω | (SparseStack.retCount I ω j : ℝ) < SparseStack.a0 * s} from h)]
    · rw [if_neg h, SparseStack.indicator_of_notMem
        (show ω ∉ {ω | (SparseStack.retCount I ω j : ℝ) < SparseStack.a0 * s} from h)]
  have hE : (SparseStack.sketchLaw s b n hb).expect
      (fun ω => ((SparseStack.badSet I ω).card : ℝ)) ≤
      I.card * Real.exp (-(s : ℝ) / 576) := by
    rw [SparseFock.FiniteLaw.expect_congr _ hcard, SparseStack.expect_sum]
    calc ∑ j ∈ I, (SparseStack.sketchLaw s b n hb).expect
          (SparseFock.FiniteLaw.indicator
            {ω | (SparseStack.retCount I ω j : ℝ) < SparseStack.a0 * s})
        ≤ ∑ _j ∈ I, Real.exp (-(s : ℝ) / 576) :=
          Finset.sum_le_sum (fun j hj => prob_retCount_lt_le_sharp hb I hIb hj)
      _ = I.card * Real.exp (-(s : ℝ) / 576) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos I.card with hN | hN
  · have hempty : {ω : SketchSample s b n |
        (I.card : ℝ) * Real.exp (-(s : ℝ) / 1152) < (SparseStack.badSet I ω).card} = ∅ := by
      ext ω
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hω
      have hω' : (I.card : ℝ) * Real.exp (-(s : ℝ) / 1152) < (SparseStack.badSet I ω).card := hω
      have h1 : (SparseStack.badSet I ω).card ≤ I.card :=
        Finset.card_le_card (SparseStack.badSet_subset I ω)
      rw [hN] at h1 hω'
      have h2 : (SparseStack.badSet I ω).card = 0 := by omega
      rw [h2] at hω'
      norm_num at hω'
    rw [hempty, SparseFock.FiniteLaw.prob_empty]
    exact he.le
  · have hthr : 0 < (I.card : ℝ) * Real.exp (-(s : ℝ) / 1152) := by
      have : (0 : ℝ) < I.card := by exact_mod_cast hN
      positivity
    have hlt_le : {ω : SketchSample s b n |
        (I.card : ℝ) * Real.exp (-(s : ℝ) / 1152) < (SparseStack.badSet I ω).card} ⊆
        {ω | (I.card : ℝ) * Real.exp (-(s : ℝ) / 1152) ≤ (SparseStack.badSet I ω).card} := by
      intro _ hω
      exact le_of_lt (Set.mem_ofPred.mp hω)
    calc (SparseStack.sketchLaw s b n hb).prob
          {ω | (I.card : ℝ) * Real.exp (-(s : ℝ) / 1152) < (SparseStack.badSet I ω).card}
        ≤ (SparseStack.sketchLaw s b n hb).prob
          {ω | (I.card : ℝ) * Real.exp (-(s : ℝ) / 1152) ≤ (SparseStack.badSet I ω).card} :=
          SparseFock.FiniteLaw.prob_mono _ hlt_le
      _ ≤ (SparseStack.sketchLaw s b n hb).expect
            (fun ω => ((SparseStack.badSet I ω).card : ℝ)) /
            ((I.card : ℝ) * Real.exp (-(s : ℝ) / 1152)) :=
          SparseFock.FiniteLaw.markov _ (fun _ => Nat.cast_nonneg _) hthr
      _ ≤ (I.card * Real.exp (-(s : ℝ) / 576)) /
            ((I.card : ℝ) * Real.exp (-(s : ℝ) / 1152)) :=
          div_le_div_of_nonneg_right hE hthr.le
      _ = Real.exp (-(s : ℝ) / 1152) := by
          rw [hsq]
          field_simp

private lemma retention2_exp_bound {R ζ₀ : ℕ} {δ_rep C_iso : ℝ}
    (hR : 2 ≤ R) (hδ₀ : 0 < δ_rep) (hδ₁ : δ_rep < 1)
    (hC_def : C_iso = 30000 + 1152 * Real.log (4 / δ_rep))
    (hζ : C_iso * Real.sqrt (Real.log (Real.exp 1 * (R : ℝ))) ≤ (ζ₀ : ℝ)) :
    Real.exp (-(ζ₀ : ℝ) / 1152) ≤ δ_rep / 4 ∧
      (R : ℝ) * ((2 : ℝ) ^ ζ₀ * (Real.exp (-(ζ₀ : ℝ) / 1152) / 16) ^ ((ζ₀ : ℝ) / 12)) ≤
        δ_rep / 4 := by
  set K_δ := Real.log (4 / δ_rep)
  have h4δ : 1 < 4 / δ_rep := by
    rw [lt_div_iff₀ hδ₀]
    linarith
  have hK_pos : 0 < K_δ := Real.log_pos h4δ
  have hexp_K : Real.exp (-K_δ) = δ_rep / 4 := by
    rw [Real.exp_neg, Real.exp_log (by linarith), inv_div]
  set L := Real.log (Real.exp 1 * (R : ℝ))
  have hR0 : (0 : ℝ) < R := by
    have : (2 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hL1 : 1 ≤ L := SparseStack.one_le_logER (by omega)
  have hsqrtL1 : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL1
  have hC_pos : 0 < C_iso := by
    rw [hC_def]
    positivity
  have hζ_ge_C : C_iso ≤ (ζ₀ : ℝ) := by
    calc C_iso = C_iso * 1 := (mul_one _).symm
      _ ≤ C_iso * Real.sqrt L := mul_le_mul_of_nonneg_left hsqrtL1 hC_pos.le
      _ ≤ (ζ₀ : ℝ) := hζ
  -- Part 1: `exp(-ζ₀ / 1152) ≤ δ_rep / 4`
  have hpart1 : Real.exp (-(ζ₀ : ℝ) / 1152) ≤ δ_rep / 4 := by
    rw [← hexp_K]
    apply Real.exp_le_exp.mpr
    rw [hC_def] at hζ_ge_C
    linarith
  refine ⟨hpart1, ?_⟩
  -- Part 2: `R * 2^ζ₀ * (exp(-ζ₀ / 1152) / 16)^(ζ₀ / 12) ≤ δ_rep / 4`
  have hpos_base : 0 < Real.exp (-(ζ₀ : ℝ) / 1152) / 16 := by positivity
  have hlog_base : Real.log (Real.exp (-(ζ₀ : ℝ) / 1152) / 16) =
      -(ζ₀ : ℝ) / 1152 - 4 * Real.log 2 := by
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp,
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  have h2ζ : (2 : ℝ) ^ ζ₀ = Real.exp ((ζ₀ : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hl2_lt1 : Real.log 2 < 1 := by
    have h := Real.log_two_lt_d9
    norm_num at h
    linarith
  have hζ_ge_30000 : (30000 : ℝ) ≤ ζ₀ := by
    rw [hC_def] at hζ_ge_C
    linarith
  have hsub_exp : (2 : ℝ) ^ ζ₀ * (Real.exp (-(ζ₀ : ℝ) / 1152) / 16) ^ ((ζ₀ : ℝ) / 12) ≤
      Real.exp (-((ζ₀ : ℝ) ^ 2) / 27648) := by
    rw [h2ζ, Real.rpow_def_of_pos hpos_base, hlog_base, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hζ0 : (0 : ℝ) ≤ ζ₀ := Nat.cast_nonneg ζ₀
    have h1 : (ζ₀ : ℝ) * Real.log 2 ≤ (ζ₀ : ℝ) :=
      mul_le_of_le_one_right hζ0 hl2_lt1.le
    have h2 : (30000 : ℝ) * ζ₀ ≤ (ζ₀ : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hζ_ge_30000 hζ0
      linarith
    linarith
  have hC2L : C_iso ^ 2 * L ≤ (ζ₀ : ℝ) ^ 2 := by
    have h1 := pow_le_pow_left₀ (by positivity) hζ 2
    rw [mul_pow, Real.sq_sqrt (by linarith)] at h1
    exact h1
  have hC2_ge : 27648 * (1 + K_δ) ≤ C_iso ^ 2 := by
    rw [hC_def]
    nlinarith [sq_nonneg K_δ]
  have hζ2_ge : 27648 * L + 27648 * K_δ ≤ (ζ₀ : ℝ) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hC2_ge (by linarith : (0 : ℝ) ≤ L)
    have h2 : K_δ ≤ K_δ * L := le_mul_of_one_le_right hK_pos.le hL1
    linarith
  have hRe := SparseStack.repnum_R_eq_exp hR0
  calc (R : ℝ) * ((2 : ℝ) ^ ζ₀ * (Real.exp (-(ζ₀ : ℝ) / 1152) / 16) ^ ((ζ₀ : ℝ) / 12))
      ≤ (R : ℝ) * Real.exp (-((ζ₀ : ℝ) ^ 2) / 27648) :=
        mul_le_mul_of_nonneg_left hsub_exp hR0.le
    _ = Real.exp (L - 1) * Real.exp (-((ζ₀ : ℝ) ^ 2) / 27648) := by rw [← hRe]
    _ = Real.exp (L - 1 + -((ζ₀ : ℝ) ^ 2) / 27648) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-K_δ) := Real.exp_le_exp.mpr (by linarith)
    _ = δ_rep / 4 := hexp_K

/-! ## 4. Helpers for Lemma 6.3 & Theorem 2.3 -/

private lemma high_sparsity_heavy {n R ζ b d : ℕ} {t₀ δ_rep C_mom M_δ η H_rep K_star β : ℝ}
    (hR : 2 ≤ R) (ht₀ : 0 < t₀) (hδ₀ : 0 < δ_rep) (hδ₁ : δ_rep < 1)
    (hC_mom : 0 < C_mom)
    (hmom_all : ∀ (ζ' b' n' D' p' : ℕ), 1 ≤ ζ' → 2 ≤ b' → 1 ≤ D' → 1 ≤ p' →
      ∀ U : Matrix (Fin n') (Fin D') ℝ, IsIsometry U →
        uniformMeanReal (SketchSample ζ' b' n')
          (fun ω =>
            let A := (sparseStackOmega ω).transpose * U
            spectralNorm (A.transpose * A - 1) ^ (2 * p')) ≤
          (D' : ℝ) * (C_mom * (Real.sqrt (((D' : ℝ) + 2 * (p' : ℝ) + 1) / ((ζ' * b' : ℕ) : ℝ)) +
            ((D' : ℝ) + 2 * (p' : ℝ) + 1) / ((ζ' * b' : ℕ) : ℝ) +
            (2 * (p' : ℝ) + 1) / (ζ' : ℝ))) ^ (2 * p'))
    (hM_def : M_δ = 2 * Real.log (4 / δ_rep) + 5)
    (hη_def : η = 1 / (18 * C_mom))
    (hH_def : H_rep = M_δ / η)
    (hK_ge : (M_δ + 2) * (1 / η + 1 / η ^ 2) ≤ K_star)
    (hβ_le : β ≤ 1 / 2)
    (hζ1 : 1 ≤ ζ)
    (hζ_high : H_rep * Real.log (Real.exp 1 * (R : ℝ)) ≤ (ζ : ℝ))
    (hk : K_star * (R : ℝ) ≤ ((ζ * b : ℕ) : ℝ))
    (hd : d ≤ R)
    (I : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ)
    (hI1 : 1 ≤ I.card) (hIR : I.card ≤ R) (hIb : 16 * I.card ≤ b)
    (hV : IsIsometry V) (hVsupp : ∀ i ∈ I, ∀ j : Fin d, V i j = 0) :
    (1 - δ_rep) ≤ uniformProb (SketchSample ζ b n)
      (fun ω => ∀ (h : Fin n → ℝ) (f : Fin d → ℝ),
        (∀ i : Fin n, i ∉ I → h i = 0) →
        β * vecSqNorm h ≤
          vecSqNorm ((sparseStackOmega ω).transpose.mulVec (h + V.mulVec f)) +
            t₀ * vecSqNorm f) := by
  have hb2 : 2 ≤ b := by omega
  have hb0 : 0 < b := by omega
  set D := I.card + d
  have hD1 : 1 ≤ D := by omega
  have hD2R : D ≤ 2 * R := by omega
  set U : Matrix (Fin n) (Fin D) ℝ := SparseStack.wPlus I V
  have hU : IsIsometry U := SparseStack.wPlus_isometry I V hV hVsupp
  set L := Real.log (Real.exp 1 * (R : ℝ))
  have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hR0 : (0 : ℝ) < R := by linarith
  have hL1 : 1 ≤ L := SparseStack.one_le_logER (by omega)
  have hL_le_R : L ≤ R := SparseStack.logER_le (by omega)
  have h4Rδ : 1 < 4 * (R : ℝ) / δ_rep := by
    rw [lt_div_iff₀ hδ₀]
    linarith
  set p : ℕ := ⌈Real.log (4 * (R : ℝ) / δ_rep)⌉₊
  have hp1 : 1 ≤ p := Nat.one_le_ceil_iff.mpr (Real.log_pos h4Rδ)
  have h4δ : 1 < 4 / δ_rep := by
    rw [lt_div_iff₀ hδ₀]
    linarith
  have hlog4δ_pos : 0 < Real.log (4 / δ_rep) := Real.log_pos h4δ
  have hM_pos : 0 < M_δ := by
    rw [hM_def]
    linarith
  have hη_pos : 0 < η := by
    rw [hη_def]
    positivity
  -- Bound `2p + 1 ≤ M_δ * L` and `D + 2p + 1 ≤ (M_δ + 2) * R`
  have h2p1_le : 2 * (p : ℝ) + 1 ≤ M_δ * L := by
    have he1 : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    have hmul_le : 4 * (R : ℝ) / δ_rep ≤ (4 / δ_rep) * (Real.exp 1 * (R : ℝ)) := by
      have h1 : 4 * (R : ℝ) / δ_rep = (4 / δ_rep) * (R : ℝ) := by ring
      rw [h1]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_mul_of_one_le_left hR0.le he1
    have hlog_le : Real.log (4 * (R : ℝ) / δ_rep) ≤ Real.log (4 / δ_rep) + L := by
      calc Real.log (4 * (R : ℝ) / δ_rep)
          ≤ Real.log ((4 / δ_rep) * (Real.exp 1 * (R : ℝ))) :=
            Real.log_le_log (by linarith) hmul_le
        _ = Real.log (4 / δ_rep) + L := Real.log_mul (by positivity) (by positivity)
    have hp_lt : (p : ℝ) < Real.log (4 * (R : ℝ) / δ_rep) + 1 :=
      Nat.ceil_lt_add_one (Real.log_pos h4Rδ).le
    rw [hM_def]
    have hkl : Real.log (4 / δ_rep) ≤ Real.log (4 / δ_rep) * L :=
      le_mul_of_one_le_right hlog4δ_pos.le hL1
    linarith
  have hDp_le : (D : ℝ) + 2 * (p : ℝ) + 1 ≤ (M_δ + 2) * R := by
    have hDR : (D : ℝ) ≤ 2 * R := by exact_mod_cast hD2R
    have hML : M_δ * L ≤ M_δ * R := mul_le_mul_of_nonneg_left hL_le_R hM_pos.le
    linarith
  -- Ratios `X ≤ η`, `√X ≤ η`, `Y ≤ η`
  have hK_pos : 0 < K_star := lt_of_lt_of_le (by positivity) hK_ge
  have hzb_pos : 0 < ((ζ * b : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hk
  set X := ((D : ℝ) + 2 * (p : ℝ) + 1) / ((ζ * b : ℕ) : ℝ)
  set Y := (2 * (p : ℝ) + 1) / (ζ : ℝ)
  have hX_le_η : X ≤ η := by
    rw [div_le_iff₀ hzb_pos]
    have h1 : (M_δ + 2) * (1 / η) ≤ K_star := by
      have : 0 ≤ (M_δ + 2) * (1 / η ^ 2) := by positivity
      linarith
    have h2 : M_δ + 2 ≤ η * K_star := by
      have := mul_le_mul_of_nonneg_left h1 hη_pos.le
      have hne : η ≠ 0 := hη_pos.ne'
      calc M_δ + 2 = η * ((M_δ + 2) * (1 / η)) := by field_simp
        _ ≤ η * K_star := this
    calc (D : ℝ) + 2 * (p : ℝ) + 1 ≤ (M_δ + 2) * R := hDp_le
      _ ≤ (η * K_star) * R := mul_le_mul_of_nonneg_right h2 hR0.le
      _ = η * (K_star * R) := by ring
      _ ≤ η * ((ζ * b : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hk hη_pos.le
  have hX_le_η2 : X ≤ η ^ 2 := by
    rw [div_le_iff₀ hzb_pos]
    have h1 : (M_δ + 2) * (1 / η ^ 2) ≤ K_star := by
      have : 0 ≤ (M_δ + 2) * (1 / η) := by positivity
      linarith
    have h2 : M_δ + 2 ≤ η ^ 2 * K_star := by
      have := mul_le_mul_of_nonneg_left h1 (sq_nonneg η)
      have hne : η ^ 2 ≠ 0 := pow_ne_zero 2 hη_pos.ne'
      calc M_δ + 2 = η ^ 2 * ((M_δ + 2) * (1 / η ^ 2)) := by field_simp
        _ ≤ η ^ 2 * K_star := this
    calc (D : ℝ) + 2 * (p : ℝ) + 1 ≤ (M_δ + 2) * R := hDp_le
      _ ≤ (η ^ 2 * K_star) * R := mul_le_mul_of_nonneg_right h2 hR0.le
      _ = η ^ 2 * (K_star * R) := by ring
      _ ≤ η ^ 2 * ((ζ * b : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hk (sq_nonneg η)
  have hsqrtX_le : Real.sqrt X ≤ η := by
    calc Real.sqrt X ≤ Real.sqrt (η ^ 2) := Real.sqrt_le_sqrt hX_le_η2
      _ = η := Real.sqrt_sq hη_pos.le
  have hY_le_η : Y ≤ η := by
    have hζ_pos : (0 : ℝ) < ζ := Nat.cast_pos.2 hζ1
    rw [div_le_iff₀ hζ_pos]
    have hMH : M_δ = η * H_rep := by
      rw [hH_def]
      field_simp
    calc 2 * (p : ℝ) + 1 ≤ M_δ * L := h2p1_le
      _ = η * (H_rep * L) := by rw [hMH]; ring
      _ ≤ η * (ζ : ℝ) := mul_le_mul_of_nonneg_left hζ_high hη_pos.le
  have hcomb : C_mom * (Real.sqrt X + X + Y) ≤ 1 / 6 := by
    have h1 : C_mom * (Real.sqrt X + X + Y) ≤ C_mom * (3 * η) :=
      mul_le_mul_of_nonneg_left (by linarith) hC_mom.le
    have h2 : C_mom * (3 * η) = 1 / 6 := by
      rw [hη_def]
      field_simp
      ring
    linarith
  -- Moment bound & Markov
  have hmom := hmom_all ζ b n D p hζ1 hb2 hD1 hp1 U hU
  rw [uniformMeanReal_eq_sketchLaw_expect hb0] at hmom
  have hmom' : (SparseStack.sketchLaw ζ b n hb0).expect
      (fun ω => ‖(SparseStack.sketchMatrix ω * U).transpose *
        (SparseStack.sketchMatrix ω * U) - 1‖ ^ (2 * p)) ≤
      (D : ℝ) * (1 / 6 : ℝ) ^ (2 * p) := by
    have heq : (SparseStack.sketchLaw ζ b n hb0).expect
        (fun ω => ‖(SparseStack.sketchMatrix ω * U).transpose *
          (SparseStack.sketchMatrix ω * U) - 1‖ ^ (2 * p)) =
        (SparseStack.sketchLaw ζ b n hb0).expect
          (fun ω => spectralNorm (((sparseStackOmega ω).transpose * U).transpose *
            ((sparseStackOmega ω).transpose * U) - 1) ^ (2 * p)) := by
      apply SparseFock.FiniteLaw.expect_congr
      intro ω
      rw [spectralNorm_eq_opNorm, sparseStackOmega_gram_eq]
    rw [heq]
    refine hmom.trans ?_
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D)
    exact pow_le_pow_left₀ (by positivity) hcomb (2 * p)
  have hprob_fail : (SparseStack.sketchLaw ζ b n hb0).prob
      {ω | (1 / 2 : ℝ) ≤ ‖(SparseStack.sketchMatrix ω * U).transpose *
        (SparseStack.sketchMatrix ω * U) - 1‖} ≤ δ_rep := by
    have hmk := SparseStack.CaseA.prob_norm_ge_le (SparseStack.sketchLaw ζ b n hb0)
      (fun ω => (SparseStack.sketchMatrix ω * U).transpose *
        (SparseStack.sketchMatrix ω * U) - 1) (2 * p) (by norm_num : (0 : ℝ) < 1 / 2)
    have hpow_div : (D : ℝ) * (1 / 6 : ℝ) ^ (2 * p) / (1 / 2 : ℝ) ^ (2 * p) =
        (D : ℝ) * (1 / 3 : ℝ) ^ (2 * p) := by
      have h16 : (1 / 6 : ℝ) = (1 / 3 : ℝ) * (1 / 2 : ℝ) := by norm_num
      rw [h16, mul_pow, ← mul_assoc, mul_div_assoc,
        div_self (pow_ne_zero (2 * p) (by norm_num : (1 / 2 : ℝ) ≠ 0)), mul_one]
    have h13_le_exp : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, one_div]
      apply inv_anti₀ (Real.exp_pos 1)
      linarith [Real.exp_one_lt_d9]
    have hpow_le : (1 / 3 : ℝ) ^ (2 * p) ≤ δ_rep / (4 * (R : ℝ)) := by
      calc (1 / 3 : ℝ) ^ (2 * p)
          ≤ Real.exp (-1) ^ (2 * p) := pow_le_pow_left₀ (by norm_num) h13_le_exp (2 * p)
        _ = Real.exp (-((2 * p : ℕ) : ℝ)) := by
            rw [← Real.exp_nat_mul]
            ring_nf
        _ ≤ Real.exp (-Real.log (4 * (R : ℝ) / δ_rep)) := by
            apply Real.exp_le_exp.mpr
            have hceil : Real.log (4 * (R : ℝ) / δ_rep) ≤ (p : ℝ) := Nat.le_ceil _
            have hp_nn : (0 : ℝ) ≤ p := Nat.cast_nonneg p
            push_cast
            linarith
        _ = δ_rep / (4 * (R : ℝ)) := by
            rw [Real.exp_neg, Real.exp_log (by linarith), inv_div]
    have hDR : (D : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hD2R
    calc (SparseStack.sketchLaw ζ b n hb0).prob
          {ω | (1 / 2 : ℝ) ≤ ‖(SparseStack.sketchMatrix ω * U).transpose *
            (SparseStack.sketchMatrix ω * U) - 1‖}
        ≤ (D : ℝ) * (1 / 6 : ℝ) ^ (2 * p) / (1 / 2 : ℝ) ^ (2 * p) :=
          hmk.trans (div_le_div_of_nonneg_right hmom' (by positivity))
      _ = (D : ℝ) * (1 / 3 : ℝ) ^ (2 * p) := hpow_div
      _ ≤ (2 * (R : ℝ)) * (δ_rep / (4 * (R : ℝ))) :=
          mul_le_mul hDR hpow_le (by positivity) (by positivity)
      _ = δ_rep / 2 := by field_simp; ring
      _ ≤ δ_rep := by linarith
  rw [uniformProb_eq_sketchLaw_prob hb0]
  apply SparseStack.one_sub_le_prob_of_prob_compl_le
  refine (SparseFock.FiniteLaw.prob_mono _ ?_).trans hprob_fail
  intro ω hω
  show (1 / 2 : ℝ) ≤ ‖(SparseStack.sketchMatrix ω * U).transpose *
    (SparseStack.sketchMatrix ω * U) - 1‖
  by_contra hlt
  have hle : ‖(SparseStack.sketchMatrix ω * U).transpose *
      (SparseStack.sketchMatrix ω * U) - 1‖ ≤ 1 - (1 / 2 : ℝ) := by linarith
  have hquad := SparseStack.CaseA.quadraticLowerBound_of_norm_le
    (SparseStack.sketchMatrix ω * U) hle
  apply hω
  intro h f hh
  set u := SparseStack.wPlusCoeff I h f
  have hUu : U.mulVec u = h + V.mulVec f := by
    rw [SparseStack.wPlus_mulVec]
    have hrest : SparseStack.restrictVec I h = h := by
      funext i
      by_cases hi : i ∈ I
      · simp [SparseStack.restrictVec, hi]
      · simp [SparseStack.restrictVec, hi, hh i hi]
    rw [hrest]
  have hu_norm : SparseStack.sqNorm u = vecSqNorm h + vecSqNorm f := by
    rw [SparseStack.sqNorm_wPlusCoeff, vecSqNorm_eq_sqNorm f]
    congr 1
    rw [vecSqNorm, Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [hh i hi])]
  have hq_u := hquad u
  change (1 / 2 : ℝ) * SparseStack.sqNorm u ≤
    SparseStack.sqNorm ((SparseStack.sketchMatrix ω * U).mulVec u) at hq_u
  rw [← Matrix.mulVec_mulVec, hUu, ← vecSqNorm_sparseStackOmega_mulVec, hu_norm] at hq_u
  have hh_nn := vecSqNorm_nonneg h
  have hf_nn := vecSqNorm_nonneg f
  linarith [hq_u, mul_le_mul_of_nonneg_right hβ_le hh_nn, mul_nonneg ht₀.le hf_nn]

private lemma loewner_of_variational {n r k : ℕ} {β t₀ : ℝ}
    (Q : Matrix (Fin n) (Fin r) ℝ) (hQ : IsIsometry Q)
    (I : Finset (Fin n)) (Y : Matrix (Fin k) (Fin r) ℝ)
    (hvar : ∀ x : Fin r → ℝ,
      β * vecSqNorm (coordVec I (Q.mulVec x)) -
          t₀ * vecSqNorm (coordVec Iᶜ (Q.mulVec x)) ≤
        vecSqNorm (Y.mulVec x)) :
    LoewnerLe (β • (1 : Matrix (Fin r) (Fin r) ℝ))
      (Y.transpose * Y +
        (β + t₀) • ((coordRows Iᶜ Q).transpose * coordRows Iᶜ Q)) := by
  unfold LoewnerLe
  set M : Matrix (Fin r) (Fin r) ℝ :=
    Y.transpose * Y + (β + t₀) • ((coordRows Iᶜ Q).transpose * coordRows Iᶜ Q) -
      β • (1 : Matrix (Fin r) (Fin r) ℝ)
  have hHerm : M.IsHermitian := by
    ext i j
    simp only [M, Matrix.conjTranspose_apply, star_trivial, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    have hY : ∑ a : Fin k, Y a j * Y a i = ∑ a : Fin k, Y a i * Y a j :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    have hC : ∑ a : Fin n, coordRows Iᶜ Q a j * coordRows Iᶜ Q a i =
        ∑ a : Fin n, coordRows Iᶜ Q a i * coordRows Iᶜ Q a j :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [hY, hC]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := Ne.symm hij
      simp [hij, hji]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm (fun x => ?_)
  have hstar : star x = x := rfl
  rw [hstar]
  have hgram : ∀ {m : ℕ} (Z : Matrix (Fin m) (Fin r) ℝ),
      dotProduct x ((Z.transpose * Z).mulVec x) = vecSqNorm (Z.mulVec x) := by
    intro m Z
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      vecSqNorm_eq_sqNorm]
    rfl
  have hCR : (coordRows Iᶜ Q).mulVec x = coordVec Iᶜ (Q.mulVec x) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, coordRows, coordVec, ite_mul, zero_mul]
    by_cases hi : i ∈ Iᶜ <;> simp [hi]
  have hsmul_dot : ∀ (c : ℝ) (Z : Matrix (Fin r) (Fin r) ℝ),
      dotProduct x ((c • Z).mulVec x) = c * dotProduct x (Z.mulVec x) := by
    intro c Z
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hone_dot : dotProduct x ((1 : Matrix (Fin r) (Fin r) ℝ).mulVec x) = vecSqNorm x := by
    rw [Matrix.one_mulVec, vecSqNorm_eq_sqNorm]
    rfl
  have hMx : dotProduct x (M.mulVec x) =
      vecSqNorm (Y.mulVec x) + (β + t₀) * vecSqNorm (coordVec Iᶜ (Q.mulVec x)) -
        β * vecSqNorm x := by
    simp only [M, Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add]
    rw [hgram Y, hsmul_dot, hgram (coordRows Iᶜ Q), hCR, hsmul_dot, hone_dot]
  have hQx : vecSqNorm x =
      vecSqNorm (coordVec I (Q.mulVec x)) + vecSqNorm (coordVec Iᶜ (Q.mulVec x)) := by
    have hiso : vecSqNorm (Q.mulVec x) = vecSqNorm x := by
      rw [vecSqNorm_eq_sqNorm, vecSqNorm_eq_sqNorm]
      exact SparseStack.CaseBLin.sqNorm_mulVec_isometry Q hQ x
    rw [← hiso, vecSqNorm_coordVec, vecSqNorm_coordVec, vecSqNorm,
      ← Finset.sum_add_sum_compl I (fun i => (Q.mulVec x i) ^ 2)]
  rw [hMx, hQx]
  linarith [hvar x]

private lemma combine_two_group_bounds {t₀ ρ₀ c SG SB SF X₁ X₂ X : ℝ}
    (ht₀₀ : 0 < t₀) (ht₀₁ : t₀ < 1 / 4)
    (hc_ge : ρ₀ ≤ c) (hc_le : c ≤ 1 / 2) (hc0 : 0 ≤ c)
    (hSG : 0 ≤ SG) (hSB : 0 ≤ SB) (hSF : 0 ≤ SF)
    (cert1 : (11 / 12 - t₀) * SG - t₀ * SB ≤ X₁ + t₀ * SF)
    (cert2 : (11 / 12 - t₀) * SB ≤ X₂ + t₀ * (SG + SF))
    (hgrp : c * (X₁ + X₂) ≤ X) :
    ρ₀ * (11 / 12 - 2 * t₀) * (SG + SB) ≤ X + t₀ * SF := by
  have hsum : (11 / 12 - 2 * t₀) * (SG + SB) ≤ X₁ + X₂ + 2 * t₀ * SF := by linarith
  have h11 : 0 ≤ (11 / 12 - 2 * t₀) * (SG + SB) :=
    mul_nonneg (by linarith) (add_nonneg hSG hSB)
  have h2t : 0 ≤ 2 * t₀ * SF := mul_nonneg (by linarith) hSF
  have k1 := mul_le_mul_of_nonneg_left hsum hc0
  have k2 := mul_le_mul_of_nonneg_right hc_ge h11
  have k3 := mul_le_mul_of_nonneg_right hc_le h2t
  linarith

end Sec6Aux

open Sec6Aux
open scoped Matrix.Norms.L2Operator

/-- **Lemma 6.1 (Norm preservation for well-isolated coordinates in a single group, p. 30).** -/
theorem lemma_6_1_SingleGroup : Lemma_6_1_SingleGroup := by
  intro t₀ δ_rep H₀ ht₀ hδ₀ _hδ₁ hH₀
  obtain ⟨C_cg, hC_cg_pos, hcg_d0, hcg_empty, hcg_main⟩ := lemma_5_4_IsolatedCrossTerm
  set δ_target := (δ_rep / 4) * t₀ / (2 * C_cg)
  have hδ_target : 0 < δ_target := by positivity
  set C₀ := 2 + 4 / δ_target
  set K₀ := 1 + 22 / δ_target ^ 2 + 64 * H₀ ^ 4 / δ_target ^ 2
  refine ⟨C₀, K₀, by positivity, by positivity, ?_⟩
  intro n R ζ₀ b d₀ hR hζ_lo hζ_hi hk hbs hd₀ I₀ V₀ hIR hV₀ hV₀_supp ω₀ G₀ B₀
  have hL1 : 1 ≤ Real.log (Real.exp 1 * (R : ℝ)) := SparseStack.one_le_logER (by omega)
  have hsqrtL1 : 1 ≤ Real.sqrt (Real.log (Real.exp 1 * (R : ℝ))) := Real.one_le_sqrt.mpr hL1
  have hC₀_gt2 : 2 < C₀ := by
    show 2 < 2 + 4 / δ_target
    have : 0 < 4 / δ_target := by positivity
    linarith
  have hζ₀_gt2 : (2 : ℝ) < ζ₀ := by nlinarith
  have hζ₀_1 : 1 ≤ ζ₀ := by
    have : (1 : ℝ) ≤ ζ₀ := by linarith
    exact_mod_cast this
  have hζ₀_pos : 0 < ζ₀ := hζ₀_1
  have hb0 : 0 < b := by omega
  rw [uniformProb_eq_sketchLaw_prob hb0]
  apply SparseStack.one_sub_le_prob_of_prob_compl_le
  -- Bound `P_ω(t₀ < spectralNorm (retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω))) ≤ δ_rep / 4`
  have hprob_cross : (SparseStack.sketchLaw ζ₀ b n hb0).prob
      {ω | t₀ < spectralNorm (retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω))} ≤
      δ_rep / 4 := by
    by_cases hdeg : I₀.card = 0 ∨ d₀ = 0
    · have hzero : ∀ ω : SketchSample ζ₀ b n,
          retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω) = 0 := by
        intro ω
        rcases hdeg with hI0 | hd0
        · rw [Finset.card_eq_zero.1 hI0]
          exact hcg_empty ζ₀ b n d₀ (mergeHeadSample ∅ ω₀ ω) V₀
        · subst hd0
          exact hcg_d0 ζ₀ b n I₀ (mergeHeadSample I₀ ω₀ ω) V₀
      have hempty : {ω : SketchSample ζ₀ b n |
          t₀ < spectralNorm (retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω))} = ∅ := by
        ext ω
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hω
        have hω' : t₀ < spectralNorm (retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω)) := hω
        rw [hzero ω, spectralNorm_eq_opNorm, norm_zero] at hω'
        linarith
      rw [hempty, SparseFock.FiniteLaw.prob_empty]
      linarith
    · push Not at hdeg
      have hI1 : 1 ≤ I₀.card := Nat.one_le_iff_ne_zero.2 hdeg.1
      have hd1 : 1 ≤ d₀ := Nat.one_le_iff_ne_zero.2 hdeg.2
      set p := ⌈Real.log (2 * Real.exp 1 * (R : ℝ))⌉₊
      have hR0 : (0 : ℝ) < R := by
        have : (2 : ℝ) ≤ R := by exact_mod_cast hR
        linarith
      have hp1 : 1 ≤ p := by
        rw [Nat.one_le_ceil_iff, SparseStack.repnum_log2eR_eq hR0]
        linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      have hplog : Real.log (2 * (d₀ : ℝ)) ≤ (p : ℝ) :=
        SparseStack.repnum_log_le_p (by exact_mod_cast hd1) (by exact_mod_cast hd₀)
      have hE := hcg_main ζ₀ b n d₀ p hζ₀_1 hbs hd1 hp1 hplog I₀ V₀ hI1 hV₀ hV₀_supp ω₀
      rw [uniformMeanReal_eq_sketchLaw_expect hb0] at hE
      have hrhs := cross_rhs_le_target hR hC_cg_pos hH₀ hδ_target rfl rfl
        hζ_lo hζ_hi hk hbs hd₀ hIR (p := p) rfl
      have hC2 : C_cg * (2 * δ_target) = (δ_rep / 4) * t₀ := by
        show C_cg * (2 * ((δ_rep / 4) * t₀ / (2 * C_cg))) = (δ_rep / 4) * t₀
        field_simp [hC_cg_pos.ne']
      rw [hC2] at hrhs
      have hE_le : (SparseStack.sketchLaw ζ₀ b n hb0).expect
          (fun ω => spectralNorm (retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω))) ≤
          (δ_rep / 4) * t₀ := hE.trans hrhs
      have hsub : {ω : SketchSample ζ₀ b n |
          t₀ < spectralNorm (retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω))} ⊆
          {ω | t₀ ≤ spectralNorm (retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω))} := by
        intro _ hω
        exact le_of_lt (Set.mem_ofPred.mp hω)
      calc (SparseStack.sketchLaw ζ₀ b n hb0).prob
            {ω | t₀ < spectralNorm (retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω))}
          ≤ (SparseStack.sketchLaw ζ₀ b n hb0).prob
            {ω | t₀ ≤ spectralNorm (retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω))} :=
            SparseFock.FiniteLaw.prob_mono _ hsub
        _ ≤ (SparseStack.sketchLaw ζ₀ b n hb0).expect
              (fun ω => spectralNorm (retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω))) / t₀ :=
            SparseFock.FiniteLaw.markov _
              (fun _ => by rw [spectralNorm_eq_opNorm]; exact norm_nonneg _) ht₀
        _ ≤ ((δ_rep / 4) * t₀) / t₀ := div_le_div_of_nonneg_right hE_le ht₀.le
        _ = δ_rep / 4 := mul_div_cancel_right₀ _ ht₀.ne'
  refine (SparseFock.FiniteLaw.prob_mono _ ?_).trans hprob_cross
  intro ω hω
  show t₀ < spectralNorm (retainedCrossGram I₀ V₀ (mergeHeadSample I₀ ω₀ ω))
  by_contra hle
  exact hω (fun h f hh => single_group_cert hζ₀_pos I₀ V₀ ω₀ ω ht₀.le (not_lt.mp hle) h f hh)

/-- **Lemma 6.2 (Two-group balls-into-bins isolation, p. 31, exact `c₁ = 1/1152`).** -/
theorem lemma_6_2_TwoGroupIsolation : Lemma_6_2_TwoGroupIsolation := by
  intro δ_rep hδ₀ hδ₁ c₁
  set C_iso := 30000 + 1152 * Real.log (4 / δ_rep)
  have h4δ : 1 < 4 / δ_rep := by
    rw [lt_div_iff₀ hδ₀]
    linarith
  have hC_pos : 0 < C_iso := by
    have := Real.log_pos h4δ
    positivity
  refine ⟨C_iso, hC_pos, ?_⟩
  intro n R ζ₀ b hR hb hζ I hIR hIb B_of
  have hb0 : 0 < b := hb
  have hc₁_eq : ∀ s : ℝ, -c₁ * s = -s / 1152 := fun s => by
    show -(1 / 1152 : ℝ) * s = -s / 1152
    ring
  obtain ⟨hexp_le, hret2_le⟩ := retention2_exp_bound hR hδ₀ hδ₁ rfl hζ
  have hB_eq : ∀ ω₁ : SketchSample ζ₀ b n, B_of ω₁ = SparseStack.badSet I ω₁ :=
    fun ω₁ => sdiff_good_eq_badSet I ω₁
  constructor
  · -- Part (i): `P(|B| ≤ |I| exp(-c₁ ζ₀)) ≥ 1 - δ_rep / 4`
    rw [uniformProb_eq_sketchLaw_prob hb0]
    apply SparseStack.one_sub_le_prob_of_prob_compl_le
    have hsub : {ω₁ : SketchSample ζ₀ b n |
        ((B_of ω₁).card : ℝ) ≤ (I.card : ℝ) * Real.exp (-c₁ * (ζ₀ : ℝ))}ᶜ ⊆
        {ω₁ | (I.card : ℝ) * Real.exp (-(ζ₀ : ℝ) / 1152) < (SparseStack.badSet I ω₁).card} := by
      intro ω₁ hω₁
      have h1 : ¬ (((B_of ω₁).card : ℝ) ≤ (I.card : ℝ) * Real.exp (-c₁ * (ζ₀ : ℝ))) := hω₁
      rw [hB_eq ω₁, hc₁_eq] at h1
      exact not_le.mp h1
    exact (SparseFock.FiniteLaw.prob_mono _ hsub).trans
      ((prob_badSet_card_le_sharp hb0 I hIb).trans hexp_le)
  · -- Part (ii): conditional on `|B| ≤ |I| exp(-c₁ ζ₀)`, Group 2 isolates all of `B`
    intro ω₁ hB_card
    rw [uniformProb_eq_sketchLaw_prob hb0]
    apply SparseStack.one_sub_le_prob_of_prob_compl_le
    set B := B_of ω₁
    have hBI : B ⊆ I := Finset.sdiff_subset
    have hBR : (B.card : ℝ) ≤ R := by
      exact_mod_cast (Finset.card_le_card hBI).trans hIR
    set π := Real.exp (-(ζ₀ : ℝ) / 1152) / 16
    have hπ0 : 0 ≤ π := by positivity
    have hπ1 : π ≤ 1 := by
      have he1 : Real.exp (-(ζ₀ : ℝ) / 1152) ≤ 1 := by
        calc Real.exp (-(ζ₀ : ℝ) / 1152) ≤ Real.exp 0 :=
              Real.exp_le_exp.mpr (by have : (0 : ℝ) ≤ ζ₀ := Nat.cast_nonneg ζ₀; linarith)
          _ = 1 := Real.exp_zero
      show Real.exp (-(ζ₀ : ℝ) / 1152) / 16 ≤ 1
      linarith
    have hπ_b : (B.card : ℝ) ≤ π * b := by
      rw [hc₁_eq] at hB_card
      have hIbR : (16 * I.card : ℝ) ≤ b := by exact_mod_cast hIb
      have he_nn : 0 ≤ Real.exp (-(ζ₀ : ℝ) / 1152) := (Real.exp_pos _).le
      have h16B : 16 * (B.card : ℝ) ≤ b * Real.exp (-(ζ₀ : ℝ) / 1152) := by nlinarith
      show (B.card : ℝ) ≤ Real.exp (-(ζ₀ : ℝ) / 1152) / 16 * b
      linarith
    have hsub : {ω₂ : SketchSample ζ₀ b n |
        ∀ i ∈ B, (11 / 12 : ℝ) * (ζ₀ : ℝ) ≤ (isolatedBlockCount B ω₂ i : ℝ)}ᶜ ⊆
        {ω₂ | ∃ i ∈ B, (SparseStack.retCount B ω₂ i : ℝ) < SparseStack.a0 * ζ₀} := by
      intro ω₂ hω₂
      have h1 : ¬ (∀ i ∈ B, (11 / 12 : ℝ) * (ζ₀ : ℝ) ≤ (isolatedBlockCount B ω₂ i : ℝ)) := hω₂
      push Not at h1
      obtain ⟨i, hiB, hlt⟩ := h1
      rw [isolatedBlockCount_eq_retCount B ω₂ hiB] at hlt
      exact ⟨i, hiB, hlt⟩
    have hrg2 := SparseStack.retention_group2 (s := ζ₀) hb0 B hπ0 hπ1 hπ_b
    have hmul_R : (B.card : ℝ) * (2 ^ ζ₀ * π ^ ((ζ₀ : ℝ) / 12)) ≤
        (R : ℝ) * (2 ^ ζ₀ * π ^ ((ζ₀ : ℝ) / 12)) :=
      mul_le_mul_of_nonneg_right hBR (by positivity)
    exact (SparseFock.FiniteLaw.prob_mono _ hsub).trans ((hrg2.trans hmul_R).trans hret2_le)

/-- **Lemma 6.3 (Two-group lower bound for heavy coordinates, p. 32).** -/
theorem lemma_6_3_TwoGroupHeavy : Lemma_6_3_TwoGroupHeavy := by
  intro t₀ δ_rep ht₀₀ ht₀₁ hδ₀ hδ₁
  obtain ⟨C_mom, hC_mom_pos, hmom_all⟩ := lemma_5_5_FullSketchMoment
  set M_δ := 2 * Real.log (4 / δ_rep) + 5
  have h4δ : 1 < 4 / δ_rep := by
    rw [lt_div_iff₀ hδ₀]
    linarith
  have hM_pos : 0 < M_δ := by
    have := Real.log_pos h4δ
    positivity
  set η := 1 / (18 * C_mom)
  have hη_pos : 0 < η := by positivity
  set H_rep := M_δ / η
  have hH_pos : 0 < H_rep := by positivity
  obtain ⟨C₀, K₀, hC₀_pos, hK₀_pos, h61⟩ :=
    lemma_6_1_SingleGroup t₀ δ_rep H_rep ht₀₀ hδ₀ hδ₁ hH_pos
  obtain ⟨C_iso, hC_iso_pos, h62⟩ :=
    lemma_6_2_TwoGroupIsolation δ_rep hδ₀ hδ₁
  set C_star := 3 * (C₀ + C_iso + 2)
  set K_star := 3 * K₀ + 2 * H_rep ^ 2 + (M_δ + 2) * (1 / η + 1 / η ^ 2) + 1
  set ρ₀ : ℝ := 1 / 3
  have hC_star_pos : 0 < C_star := by positivity
  have hK_star_pos : 0 < K_star := by positivity
  refine ⟨C_star, K_star, ρ₀, hC_star_pos, hK_star_pos, le_rfl, by norm_num, ?_, ?_⟩
  · show 0 < ρ₀ * (11 / 12 - 2 * t₀)
    have : ρ₀ = 1 / 3 := rfl
    linarith
  · intro n R ζ b d hR hζ hk hd I V hIR hIb hV hVsupp
    set β := ρ₀ * (11 / 12 - 2 * t₀)
    have hβ_le_half : β ≤ 1 / 2 := by
      show (1 / 3 : ℝ) * (11 / 12 - 2 * t₀) ≤ 1 / 2
      linarith
    have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
    have hR0 : (0 : ℝ) < R := by linarith
    set L := Real.log (Real.exp 1 * (R : ℝ))
    have hL1 : 1 ≤ L := SparseStack.one_le_logER (by omega)
    have hsqrtL1 : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL1
    have hζ_gt6 : (6 : ℝ) < ζ := by
      have hC6 : 6 < C_star := by
        show 6 < 3 * (C₀ + C_iso + 2)
        linarith
      nlinarith
    have hζ6 : 6 ≤ ζ := by
      have : (6 : ℝ) ≤ ζ := hζ_gt6.le
      exact_mod_cast this
    have hζ1 : 1 ≤ ζ := by omega
    have hb0 : 0 < b := by
      have hzb_pos : 0 < ((ζ * b : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hk
      have hzb_nat : 0 < ζ * b := Nat.cast_pos.1 hzb_pos
      exact Nat.pos_of_mul_pos_left hzb_nat
    -- Degenerate case `I = ∅`
    rcases Nat.eq_zero_or_pos I.card with hI0 | hI_pos
    · rw [uniformProb_eq_sketchLaw_prob hb0]
      have huniv : {ω : SketchSample ζ b n |
          ∀ (h : Fin n → ℝ) (f : Fin d → ℝ),
            (∀ i : Fin n, i ∉ I → h i = 0) →
            β * vecSqNorm h ≤
              vecSqNorm ((sparseStackOmega ω).transpose.mulVec (h + V.mulVec f)) +
                t₀ * vecSqNorm f} = Set.univ := by
        ext ω
        simp only [Set.mem_univ, iff_true]
        intro h f hh
        have hI_emp : I = ∅ := Finset.card_eq_zero.1 hI0
        have hh0 : h = 0 := by
          funext i
          exact hh i (by simp [hI_emp])
        rw [hh0, show vecSqNorm (0 : Fin n → ℝ) = 0 by simp [vecSqNorm], mul_zero]
        have h1 := vecSqNorm_nonneg ((sparseStackOmega ω).transpose.mulVec (0 + V.mulVec f))
        have h2 := vecSqNorm_nonneg f
        linarith [h1, mul_nonneg ht₀₀.le h2]
      rw [huniv, SparseFock.FiniteLaw.prob_univ]
      linarith
    · -- Nonempty head `1 ≤ I.card`
      by_cases hreg : H_rep * L ≤ (ζ : ℝ)
      · -- High-sparsity regime: `H_rep * log(e R) ≤ ζ`
        refine high_sparsity_heavy hR ht₀₀ hδ₀ hδ₁ hC_mom_pos hmom_all rfl rfl rfl ?_
          hβ_le_half hζ1 hreg hk hd I V hI_pos hIR hIb hV hVsupp
        show (M_δ + 2) * (1 / η + 1 / η ^ 2) ≤ K_star
        have : 0 ≤ 3 * K₀ + 2 * H_rep ^ 2 := by positivity
        linarith
      · -- Moderate-sparsity regime: `ζ < H_rep * log(e R)`
        have hζ_lt : (ζ : ℝ) < H_rep * L := lt_of_not_ge hreg
        set s : ℕ := ζ / 2
        have h3s : ζ ≤ 3 * s := by omega
        have h2s : 2 * s ≤ ζ := Nat.mul_div_le ζ 2
        have hζ_posR : (0 : ℝ) < ζ := Nat.cast_pos.2 hζ1
        have hc_ge : ρ₀ ≤ (s : ℝ) / ζ := by
          rw [le_div_iff₀ hζ_posR]
          have h3sR : (ζ : ℝ) ≤ 3 * (s : ℝ) := by exact_mod_cast h3s
          show (1 / 3 : ℝ) * ζ ≤ s
          linarith
        have hc_le : (s : ℝ) / ζ ≤ 1 / 2 := by
          rw [div_le_iff₀ hζ_posR]
          have h2sR : 2 * (s : ℝ) ≤ ζ := by exact_mod_cast h2s
          linarith
        have hs_ge_sum : (C₀ + C_iso + 2) * Real.sqrt L ≤ (s : ℝ) := by
          have h3sR : (ζ : ℝ) ≤ 3 * (s : ℝ) := by exact_mod_cast h3s
          have : 3 * (C₀ + C_iso + 2) * Real.sqrt L ≤ 3 * (s : ℝ) := by
            calc 3 * (C₀ + C_iso + 2) * Real.sqrt L = C_star * Real.sqrt L := rfl
              _ ≤ (ζ : ℝ) := hζ
              _ ≤ 3 * (s : ℝ) := h3sR
          linarith
        have hC₀_s : C₀ * Real.sqrt L ≤ (s : ℝ) := by
          have : 0 ≤ (C_iso + 2) * Real.sqrt L := by positivity
          linarith
        have hC_iso_s : C_iso * Real.sqrt L ≤ (s : ℝ) := by
          have : 0 ≤ (C₀ + 2) * Real.sqrt L := by positivity
          linarith
        have hs_hi : (s : ℝ) ≤ H_rep * L := by
          have hs_le_ζ : (s : ℝ) ≤ ζ := by exact_mod_cast Nat.div_le_self ζ 2
          exact hs_le_ζ.trans hζ_lt.le
        have hK₀_sb : K₀ * (R : ℝ) ≤ ((s * b : ℕ) : ℝ) := by
          have h3sb : ζ * b ≤ 3 * (s * b) := by
            calc ζ * b ≤ (3 * s) * b := Nat.mul_le_mul_right b h3s
              _ = 3 * (s * b) := by ring
          have h3sbR : ((ζ * b : ℕ) : ℝ) ≤ 3 * ((s * b : ℕ) : ℝ) := by exact_mod_cast h3sb
          have hK_ge3 : 3 * K₀ ≤ K_star := by
            show 3 * K₀ ≤ 3 * K₀ + 2 * H_rep ^ 2 + (M_δ + 2) * (1 / η + 1 / η ^ 2) + 1
            have : 0 ≤ 2 * H_rep ^ 2 + (M_δ + 2) * (1 / η + 1 / η ^ 2) + 1 := by positivity
            linarith
          have h1 := mul_le_mul_of_nonneg_right hK_ge3 hR0.le
          linarith
        have hbs : 2 * s ≤ b := by
          have hL2 : L ^ 2 ≤ 2 * R := SparseStack.repnum_L_sq_le (by linarith)
          have hζ2 : (ζ : ℝ) ^ 2 < 2 * H_rep ^ 2 * R := by
            calc (ζ : ℝ) ^ 2 < (H_rep * L) ^ 2 :=
                  pow_lt_pow_left₀ hζ_lt hζ_posR.le (by norm_num : 2 ≠ 0)
              _ = H_rep ^ 2 * L ^ 2 := by ring
              _ ≤ H_rep ^ 2 * (2 * R) := mul_le_mul_of_nonneg_left hL2 (sq_nonneg H_rep)
              _ = 2 * H_rep ^ 2 * R := by ring
          have hK_geH : 2 * H_rep ^ 2 < K_star := by
            show 2 * H_rep ^ 2 < 3 * K₀ + 2 * H_rep ^ 2 + (M_δ + 2) * (1 / η + 1 / η ^ 2) + 1
            have : 0 < 3 * K₀ + (M_δ + 2) * (1 / η + 1 / η ^ 2) + 1 := by positivity
            linarith
          have hHR_lt : 2 * H_rep ^ 2 * R < K_star * R :=
            mul_lt_mul_of_pos_right hK_geH hR0
          have hzb_eq : ((ζ * b : ℕ) : ℝ) = (ζ : ℝ) * b := Nat.cast_mul ζ b
          have hmul_lt : (ζ : ℝ) * ζ < (ζ : ℝ) * b := by linarith
          have hlt_b : (ζ : ℝ) < b := lt_of_mul_lt_mul_left hmul_lt hζ_posR.le
          have hle_b : ζ ≤ b := by exact_mod_cast hlt_b.le
          exact h2s.trans hle_b
        -- Two disjoint `s`-block groups
        let f₁ : Fin s → Fin ζ := fun t => ⟨t.1, by omega⟩
        let f₂ : Fin s → Fin ζ := fun t => ⟨s + t.1, by omega⟩
        have hf₁ : Function.Injective f₁ := by
          intro t t' htt
          have hval := congrArg Fin.val htt
          exact Fin.ext hval
        have hf₂ : Function.Injective f₂ := by
          intro t t' htt
          have hval : s + t.1 = s + t'.1 := congrArg Fin.val htt
          exact Fin.ext (by omega)
        have hdisj : ∀ t₁ t₂, f₁ t₁ ≠ f₂ t₂ := by
          intro t₁ t₂ htt
          have hval : t₁.1 = s + t₂.1 := congrArg Fin.val htt
          have := t₁.isLt
          omega
        let G_of : Finset (Fin n) → SketchSample s b n → Finset (Fin n) :=
          fun J ω' => J.filter (fun i => (11 / 12 : ℝ) * (s : ℝ) ≤ (isolatedBlockCount J ω' i : ℝ))
        let B_of : Finset (Fin n) → SketchSample s b n → Finset (Fin n) :=
          fun J ω' => J \ G_of J ω'
        let Cert : ∀ {d' : ℕ}, Finset (Fin n) → Matrix (Fin n) (Fin d') ℝ →
            SketchSample s b n → Prop :=
          fun J W ω' => ∀ (h : Fin n → ℝ) (f : Fin _ → ℝ),
            (∀ i : Fin n, i ∉ J → h i = 0) →
            (11 / 12 - t₀) * vecSqNorm (coordVec (G_of J ω') h) -
                t₀ * vecSqNorm (coordVec (B_of J ω') h) ≤
              vecSqNorm ((sparseStackOmega ω').transpose.mulVec (h + W.mulVec f)) +
                t₀ * vecSqNorm f
        let E₁ : SketchSample s b n → Prop := fun ω₁ =>
          Cert I V ω₁ ∧
            ((B_of I ω₁).card : ℝ) ≤ (I.card : ℝ) * Real.exp (-(1 / 1152 : ℝ) * (s : ℝ))
        let E₂ : SketchSample s b n → SketchSample s b n → Prop := fun ω₁ ω₂ =>
          Cert (B_of I ω₁) (SparseStack.wPlus (G_of I ω₁) V) ω₂ ∧
            ∀ i ∈ B_of I ω₁, (11 / 12 : ℝ) * (s : ℝ) ≤ (isolatedBlockCount (B_of I ω₁) ω₂ i : ℝ)
        -- Helper: unconditional single-group bound from `h61` via `prob_of_cond_mergeHead`
        have hCert_prob : ∀ {d' : ℕ} (J : Finset (Fin n)) (W : Matrix (Fin n) (Fin d') ℝ),
            d' ≤ 2 * R → J.card ≤ R → IsIsometry W → (∀ i ∈ J, ∀ j : Fin d', W i j = 0) →
            1 - δ_rep / 4 ≤ (SparseStack.sketchLaw s b n hb0).prob {ω' | Cert J W ω'} := by
          intro d' J W hd' hJR hW hWsupp
          apply prob_of_cond_mergeHead hb0 J (Cert J W)
          intro ω₀
          have hcond := h61 n R s b d' hR hC₀_s hs_hi hK₀_sb hbs hd' J W hJR hW hWsupp ω₀
          dsimp only at hcond
          rw [uniformProb_eq_sketchLaw_prob hb0] at hcond
          refine hcond.trans (SparseFock.FiniteLaw.prob_mono _ ?_)
          intro ω hω h f hh
          have hG_eq : G_of J (mergeHeadSample J ω₀ ω) = G_of J ω₀ := by
            ext i
            simp only [G_of, Finset.mem_filter]
            exact and_congr_right (fun hiJ => by rw [isolatedBlockCount_mergeHeadSample J ω₀ ω hiJ])
          have hB_eq : B_of J (mergeHeadSample J ω₀ ω) = B_of J ω₀ := by
            simp only [B_of, hG_eq]
          rw [hG_eq, hB_eq]
          exact hω h f hh
        -- Stage 1 probability `≥ 1 - δ_rep / 2`
        have h62_inst := h62 n R s b hR hb0 hC_iso_s I hIR hIb
        have h₁ : 1 - δ_rep / 2 ≤ (SparseStack.sketchLaw s b n hb0).prob {ω₁ | E₁ ω₁} := by
          have hc1 := hCert_prob I V (by omega) hIR hV hVsupp
          have hi1 := h62_inst.1
          rw [uniformProb_eq_sketchLaw_prob hb0] at hi1
          have hc1_compl : (SparseStack.sketchLaw s b n hb0).prob {ω₁ | Cert I V ω₁}ᶜ ≤
              δ_rep / 4 := by
            have := SparseFock.FiniteLaw.prob_compl (SparseStack.sketchLaw s b n hb0)
              {ω₁ | Cert I V ω₁}
            linarith
          have hi1_compl : (SparseStack.sketchLaw s b n hb0).prob
              {ω₁ | ((B_of I ω₁).card : ℝ) ≤
                (I.card : ℝ) * Real.exp (-(1 / 1152 : ℝ) * (s : ℝ))}ᶜ ≤ δ_rep / 4 := by
            have := SparseFock.FiniteLaw.prob_compl (SparseStack.sketchLaw s b n hb0)
              {ω₁ | ((B_of I ω₁).card : ℝ) ≤
                (I.card : ℝ) * Real.exp (-(1 / 1152 : ℝ) * (s : ℝ))}
            linarith [hi1]
          apply SparseStack.one_sub_le_prob_of_prob_compl_le
          have hsub : {ω₁ | E₁ ω₁}ᶜ ⊆ {ω₁ | Cert I V ω₁}ᶜ ∪
              {ω₁ | ((B_of I ω₁).card : ℝ) ≤
                (I.card : ℝ) * Real.exp (-(1 / 1152 : ℝ) * (s : ℝ))}ᶜ := by
            intro ω₁ hω₁
            exact not_and_or.mp hω₁
          calc (SparseStack.sketchLaw s b n hb0).prob {ω₁ | E₁ ω₁}ᶜ
              ≤ _ := SparseFock.FiniteLaw.prob_mono _ hsub
            _ ≤ _ := SparseStack.prob_union_le _ _ _
            _ ≤ δ_rep / 2 := by linarith
        -- Stage 2 conditional probability `≥ 1 - δ_rep / 2`
        have h₂ : ∀ ω₁ : SketchSample s b n, E₁ ω₁ →
            1 - δ_rep / 2 ≤ (SparseStack.sketchLaw s b n hb0).prob {ω₂ | E₂ ω₁ ω₂} := by
          intro ω₁ hE₁
          have hGI : G_of I ω₁ ⊆ I := Finset.filter_subset _ _
          have hBI : B_of I ω₁ ⊆ I := Finset.sdiff_subset
          have hBG : Disjoint (B_of I ω₁) (G_of I ω₁) := Finset.sdiff_disjoint
          have hGcard : (G_of I ω₁).card ≤ R := (Finset.card_le_card hGI).trans hIR
          have hBcard : (B_of I ω₁).card ≤ R := (Finset.card_le_card hBI).trans hIR
          have hc2 := hCert_prob (B_of I ω₁) (SparseStack.wPlus (G_of I ω₁) V) (by omega) hBcard
            (SparseStack.wPlus_isometry (G_of I ω₁) V hV (fun i hi => hVsupp i (hGI hi)))
            (SparseStack.wPlus_supp (B_of I ω₁) (G_of I ω₁) hBG V
              (fun i hi => hVsupp i (hBI hi)))
          have hi2 := h62_inst.2 ω₁ hE₁.2
          rw [uniformProb_eq_sketchLaw_prob hb0] at hi2
          have hc2_compl : (SparseStack.sketchLaw s b n hb0).prob
              {ω₂ | Cert (B_of I ω₁) (SparseStack.wPlus (G_of I ω₁) V) ω₂}ᶜ ≤ δ_rep / 4 := by
            have := SparseFock.FiniteLaw.prob_compl (SparseStack.sketchLaw s b n hb0)
              {ω₂ | Cert (B_of I ω₁) (SparseStack.wPlus (G_of I ω₁) V) ω₂}
            linarith
          have hi2_compl : (SparseStack.sketchLaw s b n hb0).prob
              {ω₂ | ∀ i ∈ B_of I ω₁,
                (11 / 12 : ℝ) * (s : ℝ) ≤ (isolatedBlockCount (B_of I ω₁) ω₂ i : ℝ)}ᶜ ≤
              δ_rep / 4 := by
            have := SparseFock.FiniteLaw.prob_compl (SparseStack.sketchLaw s b n hb0)
              {ω₂ | ∀ i ∈ B_of I ω₁,
                (11 / 12 : ℝ) * (s : ℝ) ≤ (isolatedBlockCount (B_of I ω₁) ω₂ i : ℝ)}
            linarith [hi2]
          apply SparseStack.one_sub_le_prob_of_prob_compl_le
          have hsub : {ω₂ | E₂ ω₁ ω₂}ᶜ ⊆
              {ω₂ | Cert (B_of I ω₁) (SparseStack.wPlus (G_of I ω₁) V) ω₂}ᶜ ∪
              {ω₂ | ∀ i ∈ B_of I ω₁,
                (11 / 12 : ℝ) * (s : ℝ) ≤ (isolatedBlockCount (B_of I ω₁) ω₂ i : ℝ)}ᶜ := by
            intro ω₂ hω₂
            exact not_and_or.mp hω₂
          calc (SparseStack.sketchLaw s b n hb0).prob {ω₂ | E₂ ω₁ ω₂}ᶜ
              ≤ _ := SparseFock.FiniteLaw.prob_mono _ hsub
            _ ≤ _ := SparseStack.prob_union_le _ _ _
            _ ≤ δ_rep / 2 := by linarith
        -- Combine via two-stage independence and group inequality
        rw [uniformProb_eq_sketchLaw_prob hb0]
        have hjoint := SparseStack.two_stage_independence hb0 f₁ f₂ hf₁ hf₂ hdisj E₁ E₂
          (δ₁ := δ_rep / 2) (δ₂ := δ_rep / 2) (by linarith) h₁ h₂
        refine (le_of_eq (by ring : 1 - δ_rep = 1 - δ_rep / 2 - δ_rep / 2)).trans
          (hjoint.trans (SparseFock.FiniteLaw.prob_mono _ ?_))
        rintro ω ⟨hE₁, hE₂⟩ h f hh
        set ω₁ := SparseStack.blockRestrict f₁ ω
        set ω₂ := SparseStack.blockRestrict f₂ ω
        set G₁ := G_of I ω₁
        set B₁ := B_of I ω₁
        have hBG : Disjoint B₁ G₁ := Finset.sdiff_disjoint
        have hBG_union : B₁ ∪ G₁ = I := by
          rw [Finset.union_comm]
          exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
        -- Group 1 certificate
        have cert1 := hE₁.1 h f hh
        -- Group 2 certificate on `h' = coordVec B₁ h` and `f' = wPlusCoeff G₁ h f`
        have hhB₁ : ∀ i : Fin n, i ∉ B₁ → coordVec B₁ h i = 0 := by
          intro i hi
          simp [coordVec, hi]
        have cert2_raw := hE₂.1 (coordVec B₁ h) (SparseStack.wPlusCoeff G₁ h f) hhB₁
        have hG₂_eq : G_of B₁ ω₂ = B₁ := by
          ext i
          simp only [G_of, Finset.mem_filter, and_iff_left_iff_imp]
          exact fun hi => hE₂.2 i hi
        have hB₂_eq : B_of B₁ ω₂ = ∅ := by
          simp only [B_of, hG₂_eq, Finset.sdiff_self]
        have hcoord_idem : coordVec B₁ (coordVec B₁ h) = coordVec B₁ h := by
          funext i
          by_cases hi : i ∈ B₁ <;> simp [coordVec, hi]
        have hcoord_emp : vecSqNorm (coordVec ∅ (coordVec B₁ h)) = 0 := by
          simp [coordVec, vecSqNorm]
        have hsplit_vec : coordVec B₁ h +
            (SparseStack.wPlus G₁ V).mulVec (SparseStack.wPlusCoeff G₁ h f) = h + V.mulVec f := by
          have hh' : ∀ i : Fin n, i ∉ B₁ ∪ G₁ → h i = 0 := by
            rw [hBG_union]
            exact hh
          exact (SparseStack.split_wPlus B₁ G₁ hBG V h hh' f).symm
        have hwcoeff_norm : vecSqNorm (SparseStack.wPlusCoeff G₁ h f) =
            vecSqNorm (coordVec G₁ h) + vecSqNorm f := by
          rw [vecSqNorm_eq_sqNorm, SparseStack.sqNorm_wPlusCoeff, vecSqNorm_coordVec,
            vecSqNorm_eq_sqNorm f]
        rw [hG₂_eq, hB₂_eq, hcoord_idem, hcoord_emp, mul_zero, sub_zero, hsplit_vec,
          hwcoeff_norm] at cert2_raw
        -- Combine Group 1 + Group 2 + group norm lower bound
        have hh_split : vecSqNorm h = vecSqNorm (coordVec G₁ h) + vecSqNorm (coordVec B₁ h) := by
          have h1 : vecSqNorm h = ∑ i ∈ I, h i ^ 2 := by
            rw [vecSqNorm]
            exact (Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [hh i hi])).symm
          rw [h1, ← hBG_union, Finset.union_comm, Finset.sum_union hBG.symm,
            vecSqNorm_coordVec, vecSqNorm_coordVec]
        have hgrp := SparseStack.sqNorm_sketch_ge_groups f₁ f₂ hf₁ hf₂ hdisj ω (h + V.mulVec f)
        rw [← vecSqNorm_sparseStackOmega_mulVec ω₁, ← vecSqNorm_sparseStackOmega_mulVec ω₂,
          ← vecSqNorm_sparseStackOmega_mulVec ω] at hgrp
        rw [hh_split]
        exact combine_two_group_bounds ht₀₀ ht₀₁ hc_ge hc_le
          (le_trans (by norm_num [ρ₀]) hc_ge)
          (vecSqNorm_nonneg _) (vecSqNorm_nonneg _) (vecSqNorm_nonneg _)
          cert1 cert2_raw hgrp

/-- **Theorem 2.3 (End-to-end heavy-coordinate preservation, pp. 9, 33).** -/
theorem theorem_2_3_HeavyPreservation : Theorem_2_3_HeavyPreservation := by
  intro t₀ δ_rep ht₀₀ ht₀₁ hδ₀ hδ₁
  obtain ⟨C_star, K_star, ρ₀, hC_pos, hK_pos, hρ_lo, _hρ_hi, _hβ_pos, h63⟩ :=
    lemma_6_3_TwoGroupHeavy t₀ δ_rep ht₀₀ ht₀₁ hδ₀ hδ₁
  set β := ρ₀ * (11 / 12 - 2 * t₀)
  have hβ_ge : (1 / 3 : ℝ) * (11 / 12 - 2 * t₀) ≤ β :=
    mul_le_mul_of_nonneg_right hρ_lo (by linarith)
  refine ⟨β, C_star, K_star, hβ_ge, hC_pos, hK_pos, ?_⟩
  intro n r ζ b hr _hrn hζ hk Q I hQ hIr hIb
  have hb0 : 0 < b := by
    have hrR : (0 : ℝ) < r := Nat.cast_pos.2 (by omega)
    have hzb_pos : 0 < ((ζ * b : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hk
    exact Nat.pos_of_mul_pos_left (Nat.cast_pos.1 hzb_pos)
  obtain ⟨d, V, BJ, hd_le, hV_iso, hV_supp, hBJ⟩ := SparseStack.background_basis Q I
  have hprob := h63 n r ζ b d hr hζ hk hd_le I V hIr hIb hV_iso hV_supp
  rw [uniformProb_eq_sketchLaw_prob hb0] at hprob ⊢
  refine hprob.trans (SparseFock.FiniteLaw.prob_mono _ ?_)
  intro ω hω
  set Y := (sparseStackOmega ω).transpose * Q
  have hvar : ∀ x : Fin r → ℝ,
      β * vecSqNorm (coordVec I (Q.mulVec x)) -
          t₀ * vecSqNorm (coordVec Iᶜ (Q.mulVec x)) ≤
        vecSqNorm (Y.mulVec x) := by
    intro x
    set h := coordVec I (Q.mulVec x)
    set f := BJ.mulVec x
    have hh : ∀ i : Fin n, i ∉ I → h i = 0 := by
      intro i hi
      simp [h, coordVec, hi]
    have hVf : V.mulVec f = coordVec Iᶜ (Q.mulVec x) := by
      rw [← hBJ x]
      funext i
      by_cases hi : i ∈ I <;> simp [coordVec, hi]
    have hsum : h + V.mulVec f = Q.mulVec x := by
      rw [hVf]
      funext i
      by_cases hi : i ∈ I <;> simp [h, coordVec, hi]
    have hnorm_f : vecSqNorm f = vecSqNorm (coordVec Iᶜ (Q.mulVec x)) := by
      have hiso : vecSqNorm (V.mulVec f) = vecSqNorm f := by
        rw [vecSqNorm_eq_sqNorm, vecSqNorm_eq_sqNorm]
        exact SparseStack.CaseBLin.sqNorm_mulVec_isometry V hV_iso f
      rw [← hiso, hVf]
    have h1 := hω h f hh
    rw [hsum, Matrix.mulVec_mulVec, hnorm_f] at h1
    linarith [h1]
  exact ⟨hvar, loewner_of_variational Q hQ I Y hvar⟩

end Osi.UpperBound
