import OsiUb.Spec
import SparseStack.Basic.Defs
import SparseStack.Prob.Sketch
import SparseStack.Sketch.Mean
import SparseStack.Cross.MatrixNorm

/-!
# Preliminaries: Subspace Singular Values, Submatrix Embeddings, and SparseStack Bridges

Connects `OsiUb.Spec` primitives (`MinEigenvalueAtLeast`, `QuadraticLowerBound`, `embedSubmatrix`,
`isolatedSubmatrixCross`, `IsRandomMatrix`, `IsIsotropic`, `sparseStackMeasure`,
`sparseStackOmega`) to Rayleigh quotients, Borel measurability, and `SparseStack`.
-/

namespace OsiUb.Prelim

open OsiUb.Spec
open scoped Matrix.Norms.L2Operator

private lemma vecSqNorm_eq_dotProduct {ι : Type} [Fintype ι] (v : ι → ℝ) :
    vecSqNorm v = dotProduct v v := by
  simp only [vecSqNorm, dotProduct, sq]

theorem vecSqNorm_nonneg {ι : Type} [Fintype ι] (v : ι → ℝ) :
    0 ≤ vecSqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `OsiUb.Spec.spectralNorm A` is definitionally `‖A‖` under `Matrix.Norms.L2Operator`. -/
theorem spectralNorm_eq_l2_opNorm {m l : Type} [Fintype m] [Fintype l] [DecidableEq l]
    (A : Matrix m l ℝ) : OsiUb.Spec.spectralNorm A = ‖A‖ := by
  rw [OsiUb.Spec.spectralNorm, Matrix.l2_opNorm_def]
  rfl

/-- Two matrices `A : Matrix m₁ l ℝ` and `B : Matrix m₂ l ℝ` with identical `ℓ₂` output norms on
all input vectors `x : l → ℝ` have equal `spectralNorm`. -/
theorem spectralNorm_eq_of_forall_mulVec_sq
    {m₁ m₂ l : Type} [Fintype m₁] [Fintype m₂] [Fintype l] [DecidableEq l]
    (A : Matrix m₁ l ℝ) (B : Matrix m₂ l ℝ)
    (heq : ∀ x : l → ℝ, (∑ i : m₁, (A.mulVec x i) ^ 2) = ∑ j : m₂, (B.mulVec x j) ^ 2) :
    OsiUb.Spec.spectralNorm A = OsiUb.Spec.spectralNorm B := by
  have hle : ∀ {p₁ p₂ : Type} [Fintype p₁] [Fintype p₂]
      (M₁ : Matrix p₁ l ℝ) (M₂ : Matrix p₂ l ℝ),
      (∀ x : l → ℝ, (∑ i : p₁, (M₁.mulVec x i) ^ 2) ≤ ∑ j : p₂, (M₂.mulVec x j) ^ 2) →
      ‖M₁‖ ≤ ‖M₂‖ := by
    intro p₁ p₂ _ _ M₁ M₂ hM
    refine SparseStack.Cross.l2_opNorm_le_of_forall M₁ (norm_nonneg M₂) (fun x => ?_)
    let xL : EuclideanSpace ℝ l := WithLp.toLp 2 x
    have hbound := ContinuousLinearMap.le_opNorm
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M₂)) xL
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq] at hsq
    have hnorm_eq : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M₂)‖ = ‖M₂‖ := rfl
    have happ_eq : ∀ j : p₂,
        ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M₂)) xL).ofLp j =
          M₂.mulVec x j := fun _ => rfl
    have hx_eq : ∀ j : l, xL.ofLp j = x j := fun _ => rfl
    simp only [hnorm_eq, happ_eq, hx_eq] at hsq
    exact (hM x).trans hsq
  rw [spectralNorm_eq_l2_opNorm, spectralNorm_eq_l2_opNorm]
  exact le_antisymm (hle A B fun x => (heq x).le) (hle B A fun x => (heq x).symm.le)

/-- Zero-padded ambient embedding `embedSubmatrix J W` preserves `IsIsometry`. -/
theorem embedSubmatrix_isIsometry {n d : ℕ} (J : Finset (Fin n)) (W : Matrix J (Fin d) ℝ)
    (hW : IsIsometry W) : IsIsometry (embedSubmatrix J W) := by
  unfold IsIsometry at hW ⊢
  ext l₁ l₂
  have hW_entry := congr_fun (congr_fun hW l₁) l₂
  simp only [Matrix.mul_apply, Matrix.transpose_apply, embedSubmatrix] at hW_entry ⊢
  rw [← hW_entry]
  have hsub : (∑ i : Fin n,
      (if h : i ∈ J then W ⟨i, h⟩ l₁ else 0) * (if h : i ∈ J then W ⟨i, h⟩ l₂ else 0)) =
      ∑ i ∈ J, (if h : i ∈ J then W ⟨i, h⟩ l₁ * W ⟨i, h⟩ l₂ else 0) := by
    rw [← Finset.sum_subset (Finset.subset_univ J)]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [hi]
    · intro i _ hi
      simp [hi]
  rw [hsub]
  refine Finset.sum_bij (fun (i : Fin n) (hi : i ∈ J) => (⟨i, hi⟩ : J))
    (fun _ _ => Finset.mem_univ _)
    (fun _ _ _ _ h => congrArg Subtype.val h)
    (fun j _ => ⟨j.1, j.2, Subtype.ext rfl⟩)
    (fun i hi => by simp [hi])

/-- If `Disjoint I J`, `embedSubmatrix J W` vanishes on `I`. -/
theorem embedSubmatrix_zero_of_disjoint {n d : ℕ} {I J : Finset (Fin n)} (hIJ : Disjoint I J)
    (W : Matrix J (Fin d) ℝ) :
    ∀ i ∈ I, ∀ l : Fin d, embedSubmatrix J W i l = 0 := by
  intro i hi l
  have hiJ : i ∉ J := Finset.disjoint_left.mp hIJ hi
  simp [embedSubmatrix, hiJ]

/-- `retainedCrossGram I V ω` vanishes on rows outside `I`. -/
theorem retainedCrossGram_zero_of_notMem {ζ b n d : ℕ} (I : Finset (Fin n))
    (V : Matrix (Fin n) (Fin d) ℝ) (ω : SketchSample ζ b n) {i : Fin n} (hi : i ∉ I)
    (l : Fin d) :
    retainedCrossGram I V ω i l = 0 := by
  unfold retainedCrossGram
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [Matrix.transpose_apply, Matrix.mul_diagonal]
  simp [hi]

/-- `isolatedSubmatrixCross I J W ω ∈ ℝ^{|I|×d}` has the exact same spectral norm as the ambient
`retainedCrossGram I (embedSubmatrix J W) ω ∈ ℝ^{n×d}`. -/
theorem spectralNorm_isolatedSubmatrixCross_eq {ζ b n d : ℕ} (I J : Finset (Fin n))
    (W : Matrix J (Fin d) ℝ) (ω : SketchSample ζ b n) :
    OsiUb.Spec.spectralNorm (isolatedSubmatrixCross I J W ω) =
      OsiUb.Spec.spectralNorm (retainedCrossGram I (embedSubmatrix J W) ω) := by
  apply spectralNorm_eq_of_forall_mulVec_sq
  intro f
  set M := retainedCrossGram I (embedSubmatrix J W) ω
  have hmul : ∀ i : I, (isolatedSubmatrixCross I J W ω).mulVec f i = M.mulVec f i.1 := by
    intro i
    rfl
  simp_rw [hmul]
  rw [Finset.univ_eq_attach,
    Finset.sum_attach I (fun i : Fin n => (M.mulVec f i) ^ 2)]
  refine Finset.sum_subset (Finset.subset_univ I) ?_
  intro i _ hi
  have hz : M.mulVec f i = 0 := by
    simp only [M, Matrix.mulVec, dotProduct, retainedCrossGram_zero_of_notMem I _ ω hi, zero_mul,
      Finset.sum_const_zero]
  simp [hz]

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

private lemma mem_rowSupport_iff {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (i : Fin n) (j : Fin k) :
    j ∈ rowSupport S i ↔ S i j ≠ 0 := by
  simp [rowSupport]

private lemma sparseStackOmega_transpose_apply {ζ b n : ℕ} (ω : SketchSample ζ b n)
    (j : Fin (ζ * b)) (i : Fin n) :
    (sparseStackOmega ω).transpose j i =
      SparseStack.sketchMatrix ω (finProdFinEquiv.symm j) i :=
  rfl

/-- Gram-matrix identity connecting `OsiUb.Spec.sparseStackOmega` (`Fin (ζ * b)`) to
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

/-- Equivalence of `MinEigenvalueAtLeast` between `OsiUb.Spec.sparseStackOmega` and
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

end OsiUb.Prelim
