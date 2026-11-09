import Osi.Spec
import SparseStack.Basic.Defs
import SparseStack.Prob.Sketch
import SparseStack.Sketch.Mean

/-!
# Preliminaries: Subspace Singular Values, Measurability, and SparseStack Bridges

Blueprint contracts connecting `Osi.Spec` primitives (`MinEigenvalueAtLeast`, `QuadraticLowerBound`,
`coordFrame`, `IsRandomMatrix`, `IsIsotropic`, `sparseStackMeasure`, `sparseStackOmega`) to
Rayleigh quotients, Borel measurability, `SparseStack`, and the `Ω = I_n` necessity witness.
-/

namespace Osi.Prelim

open Osi.Spec

private lemma vecSqNorm_eq_dotProduct {ι : Type} [Fintype ι] (v : ι → ℝ) :
    vecSqNorm v = dotProduct v v := by
  simp only [vecSqNorm, dotProduct, sq]

private lemma vecSqNorm_nonneg {ι : Type} [Fintype ι] (v : ι → ℝ) :
    0 ≤ vecSqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Equivalence between `MinEigenvalueAtLeast A α` (`λ_min(Aᴴ A) ≥ α`) and
`QuadraticLowerBound A α` (`∀ x, α ‖x‖₂² ≤ ‖A x‖₂²`). -/
theorem minEigenvalueAtLeast_iff_quadraticLowerBound
    {k r : Type} [Fintype k] [Fintype r] [DecidableEq r]
    (A : Matrix k r ℝ) (α : ℝ) :
    MinEigenvalueAtLeast A α ↔ QuadraticLowerBound A α := by
  unfold MinEigenvalueAtLeast QuadraticLowerBound
  simp only [vecSqNorm_eq_dotProduct]
  set hH := Matrix.isHermitian_conjTranspose_mul_self A
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

/-- Any non-zero vector `x` with `‖A x‖₂² < α ‖x‖₂²` refutes `MinEigenvalueAtLeast A α`. -/
theorem not_minEigenvalueAtLeast_of_witness
    {k r : Type} [Fintype k] [Fintype r] [DecidableEq r]
    (A : Matrix k r ℝ) (α : ℝ) (x : r → ℝ)
    (hx : 0 < vecSqNorm x) (hlt : vecSqNorm (A.mulVec x) < α * vecSqNorm x) :
    ¬ MinEigenvalueAtLeast A α := by
  intro h
  have hle := (minEigenvalueAtLeast_iff_quadraticLowerBound A α).mp h x
  exact not_lt_of_ge (mul_le_mul_of_nonneg_left hle hx.le) (mul_lt_mul_of_pos_left hlt hx)

/-- For every `r`-element subset `R ⊆ [n]`, `coordFrame R hR ∈ ℝ^{n×r}` is an isometry. -/
theorem coordFrame_isIsometry {n r : ℕ} (R : Finset (Fin n)) (hR : R.card = r) :
    IsIsometry (coordFrame R hR) := by
  ext j₁ j₂
  simp only [coordFrame, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  by_cases hj : j₁ = j₂
  · subst hj
    have hterm : ∀ i : Fin n,
        (if i = R.orderEmbOfFin hR j₁ then (1 : ℝ) else 0) *
          (if i = R.orderEmbOfFin hR j₁ then 1 else 0) =
          if i = R.orderEmbOfFin hR j₁ then 1 else 0 := by
      intro i
      split_ifs <;> ring
    simp [hterm]
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with h₁ h₂
    · exact absurd ((R.orderEmbOfFin hR).injective (h₁.symm.trans h₂)) hj
    · ring
    · ring
    · ring

private lemma coordFrame_mulVec_of_supported {n r : ℕ} (R : Finset (Fin n)) (hR : R.card = r)
    (y : Fin n → ℝ) (hsupp : ∀ i : Fin n, i ∉ R → y i = 0) :
    (coordFrame R hR).mulVec (fun j : Fin r => y (R.orderEmbOfFin hR j)) = y := by
  ext i
  simp only [Matrix.mulVec, dotProduct, coordFrame]
  have hterm : ∀ j : Fin r,
      (if i = R.orderEmbOfFin hR j then (1 : ℝ) else 0) * y (R.orderEmbOfFin hR j) =
        if i = R.orderEmbOfFin hR j then y i else 0 := by
    intro j
    split_ifs with hij
    · rw [← hij, one_mul]
    · rw [zero_mul]
  simp_rw [hterm]
  have hmap : ∑ j ∈ (Finset.univ : Finset (Fin r)),
      (if i = R.orderEmbOfFin hR j then y i else 0) =
      ∑ k ∈ Finset.univ.map (R.orderEmbOfFin hR).toEmbedding,
        (if i = k then y i else 0) :=
    (Finset.sum_map Finset.univ (R.orderEmbOfFin hR).toEmbedding
      (fun k => if i = k then y i else 0)).symm
  rw [hmap, Finset.map_orderEmbOfFin_univ R hR, Finset.sum_ite_eq]
  split_ifs with hi
  · rfl
  · exact (hsupp i hi).symm

private lemma vecSqNorm_comp_orderEmbOfFin {n r : ℕ} (R : Finset (Fin n)) (hR : R.card = r)
    (y : Fin n → ℝ) (hsupp : ∀ i : Fin n, i ∉ R → y i = 0) :
    vecSqNorm (fun j : Fin r => y (R.orderEmbOfFin hR j)) = vecSqNorm y := by
  simp only [vecSqNorm]
  calc ∑ j ∈ (Finset.univ : Finset (Fin r)), (y (R.orderEmbOfFin hR j)) ^ 2
      = ∑ k ∈ Finset.univ.map (R.orderEmbOfFin hR).toEmbedding, (y k) ^ 2 :=
        (Finset.sum_map Finset.univ (R.orderEmbOfFin hR).toEmbedding (fun k => (y k) ^ 2)).symm
    _ = ∑ k ∈ R, (y k) ^ 2 := by rw [Finset.map_orderEmbOfFin_univ R hR]
    _ = ∑ i ∈ (Finset.univ : Finset (Fin n)), (y i) ^ 2 := by
        refine Finset.sum_subset (Finset.subset_univ R) ?_
        intro i _ hi
        simp [hsupp i hi]

/-- Any vector `y ∈ ℝ^n` supported on `R` (`|R| = r`) with `‖y‖₂² > 0` and `‖Sᵀ y‖₂² < α ‖y‖₂²`
refutes `MinEigenvalueAtLeast (Sᵀ * coordFrame R hR) α`. -/
theorem not_minEigenvalueAtLeast_coordFrame_of_supported_witness
    {n k r : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (R : Finset (Fin n)) (hR : R.card = r)
    (α : ℝ) (y : Fin n → ℝ)
    (hsupp : ∀ i : Fin n, i ∉ R → y i = 0)
    (hy : 0 < vecSqNorm y)
    (hlt : vecSqNorm (S.transpose.mulVec y) < α * vecSqNorm y) :
    ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α := by
  let x : Fin r → ℝ := fun j => y (R.orderEmbOfFin hR j)
  have hmul : (S.transpose * coordFrame R hR).mulVec x = S.transpose.mulVec y := by
    rw [← Matrix.mulVec_mulVec, coordFrame_mulVec_of_supported R hR y hsupp]
  have hnorm : vecSqNorm x = vecSqNorm y :=
    vecSqNorm_comp_orderEmbOfFin R hR y hsupp
  apply not_minEigenvalueAtLeast_of_witness (S.transpose * coordFrame R hR) α x
  · rwa [hnorm]
  · rwa [hmul, hnorm]

/-- Entrywise measurability implies measurability of `{ω | frobSq (M ω) ≤ c}`. -/
theorem measurableSet_frobSq_le
    {Ω_prob : Type} [MeasurableSpace Ω_prob] {n k : ℕ}
    {M : Ω_prob → Matrix (Fin n) (Fin k) ℝ}
    (hM : IsRandomMatrix M) (c : ℝ) :
    MeasurableSet {ω : Ω_prob | frobSq (M ω) ≤ c} := by
  have hfrob : Measurable (fun ω : Ω_prob => frobSq (M ω)) := by
    unfold frobSq
    exact Finset.measurable_sum Finset.univ fun i _ =>
      Finset.measurable_sum Finset.univ fun j _ => (hM i j).pow_const 2
  exact measurableSet_le hfrob measurable_const

private lemma mem_rowSupport_iff {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (i : Fin n) (j : Fin k) :
    j ∈ rowSupport S i ↔ S i j ≠ 0 := by
  simp [rowSupport]

private lemma satisfiesOverlapCond_congr {n k : ℕ}
    {S₁ S₂ : Matrix (Fin n) (Fin k) ℝ}
    (h : ∀ (i : Fin n) (j : Fin k), S₁ i j ≠ 0 ↔ S₂ i j ≠ 0) (η : ℝ) :
    SatisfiesOverlapCond S₁ η ↔ SatisfiesOverlapCond S₂ η := by
  have hrow : rowSupport S₁ = rowSupport S₂ := by
    funext i
    ext j
    simp only [mem_rowSupport_iff, h i j]
  have hov : overlapPairs S₁ = overlapPairs S₂ := by
    simp only [overlapPairs, hrow]
  simp only [SatisfiesOverlapCond, overlapPairCount, hov]

private def supportPatternMatrix {n k : ℕ} (S₀ : Finset (Fin n × Fin k)) :
    Matrix (Fin n) (Fin k) ℝ :=
  fun i j => if (i, j) ∈ S₀ then 1 else 0

/-- Entrywise measurability implies measurability of `{ω | SatisfiesOverlapCond (M ω) η}`. -/
theorem measurableSet_satisfiesOverlapCond
    {Ω_prob : Type} [MeasurableSpace Ω_prob] {n k : ℕ}
    {M : Ω_prob → Matrix (Fin n) (Fin k) ℝ}
    (hM : IsRandomMatrix M) (η : ℝ) :
    MeasurableSet {ω : Ω_prob | SatisfiesOverlapCond (M ω) η} := by
  classical
  have hpat : ∀ (S₀ : Finset (Fin n × Fin k)) (i : Fin n) (j : Fin k),
      supportPatternMatrix S₀ i j ≠ 0 ↔ (i, j) ∈ S₀ := by
    intro S₀ i j
    simp only [supportPatternMatrix]
    split_ifs with hp <;> simp [hp]
  have heq : {ω : Ω_prob | SatisfiesOverlapCond (M ω) η} =
      ⋃ S₀ : Finset (Fin n × Fin k),
        {ω : Ω_prob | SatisfiesOverlapCond (supportPatternMatrix S₀) η} ∩
          ⋂ p : Fin n × Fin k, {ω : Ω_prob | M ω p.1 p.2 ≠ 0 ↔ p ∈ S₀} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro hω
      refine ⟨Finset.univ.filter (fun p : Fin n × Fin k => M ω p.1 p.2 ≠ 0), ?_, ?_⟩
      · refine (satisfiesOverlapCond_congr ?_ η).mp hω
        intro i j
        rw [hpat]
        simp
      · intro p
        simp
    · rintro ⟨S₀, hS₀, hp⟩
      refine (satisfiesOverlapCond_congr ?_ η).mpr hS₀
      intro i j
      rw [hpat]
      exact hp (i, j)
  rw [heq]
  refine MeasurableSet.iUnion fun S₀ =>
    (MeasurableSet.const _).inter (MeasurableSet.iInter fun p => ?_)
  by_cases hp : p ∈ S₀
  · have hp_set : {ω : Ω_prob | M ω p.1 p.2 ≠ 0 ↔ p ∈ S₀} =
        (fun ω : Ω_prob => M ω p.1 p.2) ⁻¹' ({0} : Set ℝ)ᶜ := by
      ext ω
      simp [hp]
    rw [hp_set]
    exact hM p.1 p.2 (measurableSet_singleton (0 : ℝ)).compl
  · have hp_set : {ω : Ω_prob | M ω p.1 p.2 ≠ 0 ↔ p ∈ S₀} =
        (fun ω : Ω_prob => M ω p.1 p.2) ⁻¹' ({0} : Set ℝ) := by
      ext ω
      simp [hp]
    rw [hp_set]
    exact hM p.1 p.2 (measurableSet_singleton (0 : ℝ))

private lemma quadraticLowerBound_iff_rat {k r : ℕ}
    (A : Matrix (Fin k) (Fin r) ℝ) (α : ℝ) :
    QuadraticLowerBound A α ↔
      ∀ q : Fin r → ℚ,
        α * vecSqNorm (fun l : Fin r => (q l : ℝ)) ≤
          vecSqNorm (A.mulVec (fun l : Fin r => (q l : ℝ))) := by
  constructor
  · intro h q
    exact h (fun l => (q l : ℝ))
  · intro h x
    have hdense : DenseRange (Pi.map (fun _ : Fin r => (Rat.cast : ℚ → ℝ))) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    have hcontL : Continuous (fun v : Fin r → ℝ => α * vecSqNorm v) := by
      unfold vecSqNorm
      exact continuous_const.mul
        (continuous_finsetSum Finset.univ fun l _ => (continuous_apply l).pow 2)
    have hcontR : Continuous (fun v : Fin r → ℝ => vecSqNorm (A.mulVec v)) := by
      unfold vecSqNorm Matrix.mulVec dotProduct
      exact continuous_finsetSum Finset.univ fun j _ =>
        (continuous_finsetSum Finset.univ fun l _ =>
          continuous_const.mul (continuous_apply l)).pow 2
    exact hdense.induction_on x (isClosed_le hcontL hcontR) h

/-- Entrywise measurability implies measurability of `{ω | MinEigenvalueAtLeast ((M ω)ᵀ Q) α}`
(via equivalence with `QuadraticLowerBound` and density of `Fin r → ℚ` in `Fin r → ℝ`). -/
theorem measurableSet_minEigenvalueAtLeast_mul
    {Ω_prob : Type} [MeasurableSpace Ω_prob] {n k r : ℕ}
    {M : Ω_prob → Matrix (Fin n) (Fin k) ℝ}
    (hM : IsRandomMatrix M) (Q : Matrix (Fin n) (Fin r) ℝ) (α : ℝ) :
    MeasurableSet {ω : Ω_prob | MinEigenvalueAtLeast ((M ω).transpose * Q) α} := by
  have heq : {ω : Ω_prob | MinEigenvalueAtLeast ((M ω).transpose * Q) α} =
      ⋂ q : Fin r → ℚ,
        {ω : Ω_prob |
          α * vecSqNorm (fun l : Fin r => (q l : ℝ)) ≤
            vecSqNorm (((M ω).transpose * Q).mulVec (fun l : Fin r => (q l : ℝ)))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter,
      minEigenvalueAtLeast_iff_quadraticLowerBound, quadraticLowerBound_iff_rat]
  rw [heq]
  refine MeasurableSet.iInter fun q => measurableSet_le measurable_const ?_
  simp only [vecSqNorm, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.measurable_sum (Finset.univ : Finset (Fin k)) fun j _ => ?_
  refine (Finset.measurable_sum (Finset.univ : Finset (Fin r)) fun l _ => ?_).pow_const 2
  refine (Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ => ?_).mul measurable_const
  exact (hM i j).mul measurable_const

/-- Isotropy `E[M Mᵀ] = I_n` implies `frobSq (M ω)` is integrable with expectation `n`. -/
theorem expected_frobSq_of_isIsotropic
    {Ω_prob : Type} [MeasurableSpace Ω_prob] {P : MeasureTheory.Measure Ω_prob} {n k : ℕ}
    {M : Ω_prob → Matrix (Fin n) (Fin k) ℝ}
    (hIso : IsIsotropic P M) :
    MeasureTheory.Integrable (fun ω => frobSq (M ω)) P ∧
      (∫ ω, frobSq (M ω) ∂P) = (n : ℝ) := by
  have hfrob : (fun ω : Ω_prob => frobSq (M ω)) =
      fun ω => ∑ i : Fin n, (M ω * (M ω).transpose) i i := by
    funext ω
    simp only [frobSq, Matrix.mul_apply, Matrix.transpose_apply, sq]
  rw [hfrob]
  constructor
  · exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ => hIso.1 i i
  · rw [MeasureTheory.integral_finsetSum Finset.univ fun i _ => hIso.1 i i]
    simp [hIso.2]

private lemma sparseStackOmega_transpose_apply {ζ b n : ℕ} (ω : SketchSample ζ b n)
    (j : Fin (ζ * b)) (i : Fin n) :
    (sparseStackOmega ω).transpose j i =
      SparseStack.sketchMatrix ω (finProdFinEquiv.symm j) i :=
  rfl

/-- Gram-matrix identity connecting `Osi.Spec.sparseStackOmega` (`Fin (ζ * b)`) to
`SparseStack.sketchMatrix` (`Fin ζ × Fin b`). -/
theorem sparseStackOmega_gram_eq_sketchMatrix_gram
    {ζ b n r : ℕ} (ω : SketchSample ζ b n) (Q : Matrix (Fin n) (Fin r) ℝ) :
    ((sparseStackOmega ω).transpose * Q).conjTranspose * ((sparseStackOmega ω).transpose * Q) =
      (SparseStack.sketchMatrix ω * Q).conjTranspose * (SparseStack.sketchMatrix ω * Q) := by
  ext l₁ l₂
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_apply,
    Matrix.transpose_apply]
  exact Equiv.sum_comp finProdFinEquiv.symm
    (fun p : Fin ζ × Fin b =>
      (SparseStack.sketchMatrix ω * Q) p l₁ * (SparseStack.sketchMatrix ω * Q) p l₂)

private lemma eigenvalues_eq_of_eq {r : Type} [Fintype r] [DecidableEq r]
    {B₁ B₂ : Matrix r r ℝ} (hEq : B₁ = B₂) (h₁ : B₁.IsHermitian) (h₂ : B₂.IsHermitian) :
    h₁.eigenvalues = h₂.eigenvalues := by
  subst hEq
  rfl

/-- Equivalence of `MinEigenvalueAtLeast` between `Osi.Spec.sparseStackOmega` and
`SparseStack.sketchMatrix`. -/
theorem minEigenvalueAtLeast_sparseStackOmega_iff
    {ζ b n r : ℕ} (ω : SketchSample ζ b n) (Q : Matrix (Fin n) (Fin r) ℝ) (α : ℝ) :
    MinEigenvalueAtLeast ((sparseStackOmega ω).transpose * Q) α ↔
      SparseStack.MinEigenvalueAtLeast (SparseStack.sketchMatrix ω * Q) α := by
  unfold MinEigenvalueAtLeast SparseStack.MinEigenvalueAtLeast
  rw [eigenvalues_eq_of_eq (sparseStackOmega_gram_eq_sketchMatrix_gram ω Q)]

/-- Outer-product identity `sparseStackOmega ω * (sparseStackOmega ω)ᵀ = sketchOmega ω * (sketchOmega ω)ᵀ`. -/
theorem sparseStackOmega_outer_eq_sketchOmega
    {ζ b n : ℕ} (ω : SketchSample ζ b n) :
    sparseStackOmega ω * (sparseStackOmega ω).transpose =
      SparseStack.sketchOmega ω * (SparseStack.sketchOmega ω).transpose := by
  ext i₁ i₂
  have hentry : ∀ (i : Fin n) (j : Fin (ζ * b)),
      sparseStackOmega ω i j = SparseStack.sketchMatrix ω (finProdFinEquiv.symm j) i :=
    fun i j => sparseStackOmega_transpose_apply ω j i
  simp only [SparseStack.sketchOmega, Matrix.transpose_transpose, Matrix.mul_apply,
    Matrix.transpose_apply, hentry]
  exact Equiv.sum_comp finProdFinEquiv.symm
    (fun p : Fin ζ × Fin b => SparseStack.sketchMatrix ω p i₁ * SparseStack.sketchMatrix ω p i₂)

/-- When `1 ≤ b`, `sparseStackMeasure ζ b n` is a probability measure. -/
theorem isProbabilityMeasure_sparseStackMeasure (ζ b n : ℕ) (hb : 1 ≤ b) :
    MeasureTheory.IsProbabilityMeasure (sparseStackMeasure ζ b n) := by
  refine ⟨?_⟩
  have : Nonempty (SketchSample ζ b n) :=
    SparseStack.sketchSample_nonempty (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)
  have hne0 : (Fintype.card (SketchSample ζ b n) : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hnetop : (Fintype.card (SketchSample ζ b n) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  simp only [sparseStackMeasure, MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.finsetSum_apply, smul_eq_mul,
    MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ _),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel hne0 hnetop

/-- Bridge between `(sparseStackMeasure ζ b n {ω | E ω}).toReal` and `uniformProb`. -/
theorem sparseStackMeasure_toReal_eq_uniformProb (ζ b n : ℕ) (hb : 1 ≤ b)
    (E : SketchSample ζ b n → Prop) :
    ((sparseStackMeasure ζ b n) {ω : SketchSample ζ b n | E ω}).toReal =
      uniformProb (SketchSample ζ b n) E := by
  classical
  have hb0 : 0 < b := Nat.lt_of_lt_of_le Nat.zero_lt_one hb
  have hunif : uniformProb (SketchSample ζ b n) E =
      (SparseStack.sketchLaw ζ b n hb0).prob {ω | E ω} :=
    SparseStack.uniformProb_eq_prob hb0 E
  have hfin : ∀ ω ∈ (Finset.univ : Finset (SketchSample ζ b n)),
      (MeasureTheory.Measure.dirac ω) {ω' : SketchSample ζ b n | E ω'} ≠ ⊤ := by
    intro ω _
    rw [MeasureTheory.Measure.dirac_apply]
    by_cases hω : E ω <;> simp [hω]
  rw [hunif, SparseFock.FiniteLaw.prob, SparseStack.sketchLaw_expect_eq_sum]
  simp only [sparseStackMeasure, MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.finsetSum_apply, smul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum hfin, div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [MeasureTheory.Measure.dirac_apply]
  by_cases hω : E ω <;> simp [SparseFock.FiniteLaw.indicator, hω]

/-- `sparseStackOmega` is entrywise measurable on `SketchSample ζ b n`. -/
theorem isRandomMatrix_sparseStackOmega (ζ b n : ℕ) :
    IsRandomMatrix (sparseStackOmega (ζ := ζ) (b := b) (n := n)) :=
  fun _ _ => Measurable.of_discrete

/-- Every realization of `sparseStackOmega` has row support size at most `ζ`. -/
theorem rowSupport_sparseStackOmega_le (ζ b n : ℕ) (ω : SketchSample ζ b n) (i : Fin n) :
    (rowSupport (sparseStackOmega ω) i).card ≤ ζ := by
  have hsub : rowSupport (sparseStackOmega ω) i ⊆
      Finset.univ.image (fun t : Fin ζ => finProdFinEquiv (t, ω.1 t i)) := by
    intro j hj
    rw [mem_rowSupport_iff] at hj
    have hp : ω.1 (finProdFinEquiv.symm j).1 i = (finProdFinEquiv.symm j).2 := by
      by_contra hne
      unfold sparseStackOmega at hj
      dsimp only at hj
      rw [if_neg hne, mul_zero] at hj
      exact hj rfl
    rw [Finset.mem_image]
    refine ⟨(finProdFinEquiv.symm j).1, Finset.mem_univ _, ?_⟩
    rw [hp, Prod.mk.eta, Equiv.apply_symm_apply]
  calc (rowSupport (sparseStackOmega ω) i).card
      ≤ (Finset.univ.image (fun t : Fin ζ => finProdFinEquiv (t, ω.1 t i))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin ζ)).card := Finset.card_image_le
    _ = ζ := by simp

/-- `sparseStackOmega` is `ζ`-row-sparse a.s. under `sparseStackMeasure ζ b n`. -/
theorem isRowSparse_sparseStackOmega (ζ b n : ℕ) :
    IsRowSparse (sparseStackMeasure ζ b n) (sparseStackOmega (ζ := ζ) (b := b) (n := n)) ζ :=
  Filter.Eventually.of_forall fun ω i => rowSupport_sparseStackOmega_le ζ b n ω i

private lemma integral_sparseStackMeasure {ζ b n : ℕ} (hb : 1 ≤ b)
    (f : SketchSample ζ b n → ℝ) :
    (∫ ω, f ω ∂(sparseStackMeasure ζ b n)) =
      (Fintype.card (SketchSample ζ b n) : ℝ)⁻¹ * ∑ ω : SketchSample ζ b n, f ω := by
  have _ := isProbabilityMeasure_sparseStackMeasure ζ b n hb
  unfold sparseStackMeasure
  rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, MeasureTheory.integral_finsetSum_measure fun _ _ =>
      MeasureTheory.Integrable.of_finite]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  exact MeasureTheory.integral_dirac f ω

/-- `sparseStackOmega` is isotropic under `sparseStackMeasure ζ b n` whenever `1 ≤ ζ` and `1 ≤ b`. -/
theorem isIsotropic_sparseStackOmega (ζ b n : ℕ) (hζ : 1 ≤ ζ) (hb : 1 ≤ b) :
    IsIsotropic (sparseStackMeasure ζ b n) (sparseStackOmega (ζ := ζ) (b := b) (n := n)) := by
  have : MeasureTheory.IsProbabilityMeasure (sparseStackMeasure ζ b n) :=
    isProbabilityMeasure_sparseStackMeasure ζ b n hb
  constructor
  · intro _ _
    exact MeasureTheory.Integrable.of_finite
  · intro i j
    rw [integral_sparseStackMeasure hb]
    have hmean := congr_fun (congr_fun
      (SparseStack.mean_gram_eq_one (n := n)
        (Nat.lt_of_lt_of_le Nat.zero_lt_one hζ)
        (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)) i) j
    simp only [SparseStack.uniformMeanMatrix, Matrix.smul_apply, Matrix.sum_apply,
      smul_eq_mul] at hmean
    rw [← hmean]
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    rw [sparseStackOmega_outer_eq_sketchOmega ω]
    simp [SparseStack.sketchOmega]

private lemma rowSupport_one_subset {n : ℕ} (i : Fin n) :
    rowSupport (1 : Matrix (Fin n) (Fin n) ℝ) i ⊆ {i} := by
  intro j hj
  rw [mem_rowSupport_iff, Matrix.one_apply] at hj
  rw [Finset.mem_singleton]
  by_contra hji
  exact hj (if_neg (Ne.symm hji))

private lemma overlapPairCount_one (n : ℕ) :
    overlapPairCount (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  unfold overlapPairCount
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro uv huv
  unfold overlapPairs at huv
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at huv
  have hle : (rowSupport (1 : Matrix (Fin n) (Fin n) ℝ) uv.1 ∩
      rowSupport (1 : Matrix (Fin n) (Fin n) ℝ) uv.2).card ≤ 1 := by
    calc (rowSupport (1 : Matrix (Fin n) (Fin n) ℝ) uv.1 ∩
          rowSupport (1 : Matrix (Fin n) (Fin n) ℝ) uv.2).card
        ≤ (rowSupport (1 : Matrix (Fin n) (Fin n) ℝ) uv.1).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ ≤ ({uv.1} : Finset (Fin n)).card :=
          Finset.card_le_card (rowSupport_one_subset uv.1)
      _ = 1 := Finset.card_singleton uv.1
  exact absurd huv.2 (by omega)

private lemma minEigenvalueAtLeast_of_isIsometry {n r : ℕ}
    {Q : Matrix (Fin n) (Fin r) ℝ} (hQ : IsIsometry Q) {α : ℝ} (hα : α ≤ 1) :
    MinEigenvalueAtLeast Q α := by
  rw [minEigenvalueAtLeast_iff_quadraticLowerBound]
  intro x
  have hnorm : vecSqNorm (Q.mulVec x) = vecSqNorm x := by
    simp only [vecSqNorm_eq_dotProduct]
    calc dotProduct (Q.mulVec x) (Q.mulVec x)
        = dotProduct (Matrix.vecMul x Q.transpose) (Q.mulVec x) := by
          rw [Matrix.vecMul_transpose]
      _ = dotProduct x (Q.transpose.mulVec (Q.mulVec x)) :=
          (Matrix.dotProduct_mulVec _ _ _).symm
      _ = dotProduct x ((Q.transpose * Q).mulVec x) := by rw [Matrix.mulVec_mulVec]
      _ = dotProduct x x := by rw [hQ, Matrix.one_mulVec]
  rw [hnorm]
  calc α * vecSqNorm x ≤ 1 * vecSqNorm x :=
        mul_le_mul_of_nonneg_right hα (vecSqNorm_nonneg x)
    _ = vecSqNorm x := one_mul _

/-- Proof of `Theorem_1_3_NecessityOfAmbientBound` (`Ω = I_n` on `PUnit` when `n ≤ K r`). -/
theorem theorem_1_3_NecessityOfAmbientBound : Theorem_1_3_NecessityOfAmbientBound := by
  intro K α _hK _hα0 hα1 n r _hr _hrn hn
  let P : MeasureTheory.Measure PUnit := MeasureTheory.Measure.dirac PUnit.unit
  let M : PUnit → Matrix (Fin n) (Fin n) ℝ := fun _ => 1
  have hOSI1 : IsOSIWithProb P M r α 1 := by
    intro Q hQ
    have hmem : PUnit.unit ∈ {ω : PUnit | MinEigenvalueAtLeast ((M ω).transpose * Q) α} := by
      simp only [Set.mem_ofPred_eq, M, Matrix.transpose_one, Matrix.one_mul]
      exact minEigenvalueAtLeast_of_isIsometry hQ hα1
    rw [MeasureTheory.Measure.dirac_apply_of_mem hmem]
    norm_num
  refine ⟨inferInstance, hn, ?_, ?_, ?_, ?_, hOSI1, ?_⟩
  · intro _ _
    exact measurable_const
  · constructor
    · intro _ _
      exact MeasureTheory.integrable_const _
    · intro i j
      simp [Matrix.transpose_one]
  · refine Filter.Eventually.of_forall fun _ i => ?_
    calc (rowSupport (1 : Matrix (Fin n) (Fin n) ℝ) i).card
        ≤ ({i} : Finset (Fin n)).card := Finset.card_le_card (rowSupport_one_subset i)
      _ = 1 := Finset.card_singleton i
  · intro η hη
    unfold SatisfiesOverlapWhp
    have hmem : PUnit.unit ∈ {ω : PUnit | SatisfiesOverlapCond (M ω) η} := by
      simp only [Set.mem_ofPred_eq, SatisfiesOverlapCond, M, overlapPairCount_one, Nat.cast_zero]
      positivity
    rw [MeasureTheory.Measure.dirac_apply_of_mem hmem]
    norm_num
  · intro Q hQ
    linarith [hOSI1 Q hQ]

end Osi.Prelim
