import Osi.Spec
import Osi.Prelim.SubspaceSing
import SparseStack.IidNorm
import SparseStack.CrossGram
import SparseStack.External.StackMoment

/-!
# Section 5: Operator-Norm Bounds via Sparse Fock Moments

Proves `Lemma_5_3_IidOpNorm`, `Lemma_5_4_IsolatedCrossTerm`, and `Lemma_5_5_FullSketchMoment`
for general moment order `p ≥ max{1, log(2 d)}` (`p ≥ 1`).
-/

namespace Osi.UpperBound

open Osi.Spec
open scoped Matrix.Norms.L2Operator

/-! ### Bridge helpers between `Osi.Spec` and `SparseStack` / `SparseFock` -/

private lemma spectralNorm_eq_l2_opNorm {m l : Type} [Fintype m] [Fintype l] [DecidableEq l]
    (A : Matrix m l ℝ) : Osi.Spec.spectralNorm A = ‖A‖ := by
  rw [Osi.Spec.spectralNorm, Matrix.l2_opNorm_def]
  rfl

private lemma signValue_eq_sparseStack (β : Bool) :
    Osi.Spec.signValue β = SparseStack.signValue β := by
  cases β <;> rfl

private lemma sparseStackOmega_transpose_apply {ζ b n : ℕ} (ω : SketchSample ζ b n)
    (j : Fin (ζ * b)) (i : Fin n) :
    (sparseStackOmega ω).transpose j i =
      SparseStack.sketchMatrix ω (finProdFinEquiv.symm j) i := by
  simp only [Matrix.transpose_apply, sparseStackOmega, SparseStack.sketchMatrix,
    signValue_eq_sparseStack]

private lemma uniformMeanReal_sketchSample_eq_expect {ζ b n : ℕ} (hb : 0 < b)
    (f : SketchSample ζ b n → ℝ) :
    uniformMeanReal (SketchSample ζ b n) f = (SparseStack.sketchLaw ζ b n hb).expect f := by
  rw [SparseStack.sketchLaw_expect_eq_sum hb f, uniformMeanReal, div_eq_inv_mul]

/-! ### Helpers for `lemma_5_3_IidOpNorm` -/

private def mapOutcome {B : ℕ} (u : Fin (2 * B)) : SparseFock.EtaOutcome :=
  if u.val = 0 then .pos else if u.val = 1 then .neg else .zero

private lemma iidTernaryEntry_eq_eta_div_sqrt {B : ℕ} (hB : 2 ≤ B) (u : Fin (2 * B)) :
    iidTernaryEntry u = SparseFock.TernaryJacobi.eta B (mapOutcome u) / Real.sqrt (B : ℝ) := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hsqrt : Real.sqrt (B : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hBpos).ne'
  unfold iidTernaryEntry mapOutcome
  by_cases h0 : u.val = 0
  · simp [h0, SparseFock.TernaryJacobi.eta, div_self hsqrt]
  · by_cases h1 : u.val = 1
    · simp [h1, SparseFock.TernaryJacobi.eta, neg_div, div_self hsqrt]
    · simp [h0, h1, SparseFock.TernaryJacobi.eta]

private lemma iidTernaryMatrix_eq_iidMatrix {m n B : ℕ} (hB : 2 ≤ B)
    (ω : IidTernarySample m n B) :
    iidTernaryMatrix ω = SparseStack.iidMatrix B (fun p => mapOutcome (ω p.1 p.2)) := by
  ext ℓ j
  exact iidTernaryEntry_eq_eta_div_sqrt hB (ω ℓ j)

private lemma sum_mapOutcome_indicator {B : ℕ} (hB : 2 ≤ B) (y : SparseFock.EtaOutcome) :
    ∑ u : Fin (2 * B), (2 * (B : ℝ))⁻¹ * (if mapOutcome u = y then (1 : ℝ) else 0) =
      SparseFock.TernaryJacobi.mass B y := by
  have hpos : ∑ u : Fin (2 * B), (if mapOutcome u = .pos then (1 : ℝ) else 0) = 1 := by
    rw [Fintype.sum_eq_single (⟨0, by omega⟩ : Fin (2 * B))]
    · simp [mapOutcome]
    · intro u hu
      have hu0 : u.val ≠ 0 := fun h => hu (Fin.ext h)
      unfold mapOutcome
      by_cases hu1 : u.val = 1 <;> simp [hu0, hu1]
  have hneg : ∑ u : Fin (2 * B), (if mapOutcome u = .neg then (1 : ℝ) else 0) = 1 := by
    rw [Fintype.sum_eq_single (⟨1, by omega⟩ : Fin (2 * B))]
    · simp [mapOutcome]
    · intro u hu
      have hu1 : u.val ≠ 1 := fun h => hu (Fin.ext h)
      unfold mapOutcome
      by_cases hu0 : u.val = 0 <;> simp [hu0, hu1]
  have htot : (∑ u : Fin (2 * B), (if mapOutcome u = .neg then (1 : ℝ) else 0)) +
      (∑ u : Fin (2 * B), (if mapOutcome u = .zero then (1 : ℝ) else 0)) +
      (∑ u : Fin (2 * B), (if mapOutcome u = .pos then (1 : ℝ) else 0)) = 2 * (B : ℝ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have h1 : ∀ u : Fin (2 * B),
        (if mapOutcome u = .neg then (1 : ℝ) else 0) +
          (if mapOutcome u = .zero then (1 : ℝ) else 0) +
          (if mapOutcome u = .pos then (1 : ℝ) else 0) = 1 := by
      intro u
      cases mapOutcome u <;> simp
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
  rw [← Finset.mul_sum]
  cases y with
  | neg =>
    rw [hneg, SparseFock.TernaryJacobi.mass]
    field_simp
  | zero =>
    have hzero : ∑ u : Fin (2 * B), (if mapOutcome u = .zero then (1 : ℝ) else 0) =
        2 * (B : ℝ) - 2 := by linarith
    rw [hzero, SparseFock.TernaryJacobi.mass]
    field_simp
  | pos =>
    rw [hpos, SparseFock.TernaryJacobi.mass]
    field_simp

private lemma uniformMeanReal_iidTernarySample_eq_expect {m n B : ℕ} (hB : 2 ≤ B) (hB1 : 1 < B)
    (G : SparseFock.ProductFock.Configuration m n → ℝ) :
    uniformMeanReal (IidTernarySample m n B) (fun ω => G (fun p => mapOutcome (ω p.1 p.2))) =
      (SparseFock.ProductFock.iidLaw B hB1 m n).expect G := by
  have hcard : Fintype.card (IidTernarySample m n B) =
      (2 * B) ^ Fintype.card (Fin m × Fin n) := by
    rw [Fintype.card_congr (Equiv.curry (Fin m) (Fin n) (Fin (2 * B))).symm,
      Fintype.card_fun, Fintype.card_fin]
  have hinv : (Fintype.card (IidTernarySample m n B) : ℝ)⁻¹ =
      ∏ _p : Fin m × Fin n, (2 * (B : ℝ))⁻¹ := by
    rw [hcard, Finset.prod_const, Finset.card_univ]
    push_cast
    rw [← inv_pow]
  have hcurry : (∑ ω : IidTernarySample m n B, G (fun p => mapOutcome (ω p.1 p.2))) =
      ∑ x : Fin m × Fin n → Fin (2 * B), G (fun p => mapOutcome (x p)) :=
    ((Equiv.curry (Fin m) (Fin n) (Fin (2 * B))).sum_comp
      (fun ω => G (fun p => mapOutcome (ω p.1 p.2)))).symm
  have hdecomp : ∀ y : SparseFock.ProductFock.Configuration m n,
      G y = ∑ z : SparseFock.ProductFock.Configuration m n,
        (∏ p : Fin m × Fin n, if y p = z p then (1 : ℝ) else 0) * G z := by
    intro y
    rw [Fintype.sum_eq_single y]
    · simp
    · intro z hzy
      have hex : ∃ p, y p ≠ z p := by
        by_contra hall
        apply hzy
        funext p
        by_contra hp
        exact hall ⟨p, Ne.symm hp⟩
      obtain ⟨p, hp⟩ := hex
      rw [Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp), zero_mul]
  rw [uniformMeanReal, hinv, hcurry, Finset.mul_sum]
  have hexpand : ∀ x : Fin m × Fin n → Fin (2 * B),
      (∏ _p : Fin m × Fin n, (2 * (B : ℝ))⁻¹) * G (fun p => mapOutcome (x p)) =
        ∑ z : SparseFock.ProductFock.Configuration m n,
          (∏ p : Fin m × Fin n,
            (2 * (B : ℝ))⁻¹ * (if mapOutcome (x p) = z p then (1 : ℝ) else 0)) * G z := by
    intro x
    rw [hdecomp (fun p => mapOutcome (x p)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [← mul_assoc, ← Finset.prod_mul_distrib]
  simp_rw [hexpand]
  rw [Finset.sum_comm, SparseFock.FiniteLaw.expect]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.sum_mul]
  congr 1
  rw [← Fintype.prod_sum (fun (_p : Fin m × Fin n) (u : Fin (2 * B)) =>
    (2 * (B : ℝ))⁻¹ * (if mapOutcome u = z _p then (1 : ℝ) else 0))]
  rw [SparseFock.ProductFock.iidLaw_weight]
  apply Finset.prod_congr rfl
  intro p _
  exact sum_mapOutcome_indicator hB (z p)

/-! ### Helpers for `lemma_5_4_IsolatedCrossTerm` and `lemma_5_5_FullSketchMoment` -/

private lemma retainedCrossGram_eq_crossGram {ζ b n d : ℕ} (I : Finset (Fin n))
    (V : Matrix (Fin n) (Fin d) ℝ) (ω : SketchSample ζ b n) :
    retainedCrossGram I V ω = SparseStack.crossGram I V ω := by
  have hTP : ∀ (j : Fin (ζ * b)) (i : Fin n),
      (retainUniqueMatrix I ω * (sparseStackOmega ω).transpose) j i =
        (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω)
          (finProdFinEquiv.symm j) i := by
    intro j i
    rw [retainUniqueMatrix, SparseStack.retainMatrix, Matrix.diagonal_mul,
      Matrix.diagonal_mul, sparseStackOmega_transpose_apply]
    rfl
  have hL : ∀ (j : Fin (ζ * b)) (i : Fin n),
      (retainUniqueMatrix I ω * (sparseStackOmega ω).transpose *
        Matrix.diagonal (fun i' : Fin n => if i' ∈ I then (1 : ℝ) else 0)) j i =
        (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω *
          SparseStack.coordProj I) (finProdFinEquiv.symm j) i := by
    intro j i
    rw [SparseStack.coordProj, Matrix.mul_diagonal, Matrix.mul_diagonal, hTP]
  have hR : ∀ (j : Fin (ζ * b)) (l : Fin d),
      (retainUniqueMatrix I ω * (sparseStackOmega ω).transpose * V) j l =
        (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω * V)
          (finProdFinEquiv.symm j) l := by
    intro j l
    simp only [Matrix.mul_apply, hTP]
  ext i l
  rw [retainedCrossGram, SparseStack.crossGram, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, hL, hR]
  exact Equiv.sum_comp finProdFinEquiv.symm fun p =>
    (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω * SparseStack.coordProj I) p i *
      (SparseStack.retainMatrix I ω * SparseStack.sketchMatrix ω * V) p l

private lemma sparseStackOmega_gram_eq {ζ b n D : ℕ} (ω : SketchSample ζ b n)
    (U : Matrix (Fin n) (Fin D) ℝ) :
    ((sparseStackOmega ω).transpose * U).transpose * ((sparseStackOmega ω).transpose * U) =
      (SparseStack.sketchMatrix ω * U).transpose * (SparseStack.sketchMatrix ω * U) := by
  have hAU : ∀ (j : Fin (ζ * b)) (l : Fin D),
      ((sparseStackOmega ω).transpose * U) j l =
        (SparseStack.sketchMatrix ω * U) (finProdFinEquiv.symm j) l := by
    intro j l
    simp only [Matrix.mul_apply, sparseStackOmega_transpose_apply]
  ext l₁ l₂
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, hAU]
  exact Equiv.sum_comp finProdFinEquiv.symm fun p =>
    (SparseStack.sketchMatrix ω * U) p l₁ * (SparseStack.sketchMatrix ω * U) p l₂

/-! ### Main Section 5 Contracts -/

/-- **Lemma 5.3 (Expected squared operator norm in the independent-entry model, p. 25).** -/
theorem lemma_5_3_IidOpNorm : Lemma_5_3_IidOpNorm := by
  refine ⟨2944, by norm_num, ?_⟩
  intro a B n d p hB ha hd hp hplog W hW
  have hB1 : 1 < B := by omega
  set p' : ℕ := max p 64
  have hp'64 : 64 ≤ p' := Nat.le_max_right p 64
  have hpp' : (p : ℝ) ≤ (p' : ℝ) := by exact_mod_cast Nat.le_max_left p 64
  have hplog' : Real.log (2 * (d : ℝ)) ≤ (p' : ℝ) := hplog.trans hpp'
  have hp'le : (p' : ℝ) ≤ 64 * (p : ℝ) := by
    exact_mod_cast (show p' ≤ 64 * p by omega)
  have hfn : (fun ω : IidTernarySample (a * B) n B =>
      spectralNorm (iidTernaryMatrix ω * W) ^ 2) =
      (fun ω => ‖SparseStack.iidMatrix B (fun s => mapOutcome (ω s.1 s.2)) * W‖ ^ 2) := by
    funext ω
    rw [spectralNorm_eq_l2_opNorm, iidTernaryMatrix_eq_iidMatrix hB]
  rw [hfn, uniformMeanReal_iidTernarySample_eq_expect hB hB1
    (fun x => ‖SparseStack.iidMatrix B x * W‖ ^ 2)]
  have href := SparseStack.iid_norm_refined hB1 ha W hW hd p' hp'64 hplog'
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdiv : ((d : ℝ) + 2 * (p' : ℝ) + 1) / (B : ℝ) ≤
      64 * (((d : ℝ) + 2 * (p : ℝ) + 1) / (B : ℝ)) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg B)
  linarith

/-- **Lemma 5.4 (Cross-term operator norm on isolated buckets, p. 27).** -/
theorem lemma_5_4_IsolatedCrossTerm : Lemma_5_4_IsolatedCrossTerm := by
  refine ⟨180, by norm_num, ?_, ?_, ?_⟩
  · intro ζ b n I ω V
    ext i j
    exact Fin.elim0 j
  · intro ζ b n d ω V
    unfold retainedCrossGram
    simp
  · intro ζ b n d p hζ hbζ hd hp hplog I V hI hV hVsupp ω₀
    have hb0 : 0 < b := by omega
    set p' : ℕ := max p 64
    have hp'64 : 64 ≤ p' := Nat.le_max_right p 64
    have hpp' : (p : ℝ) ≤ (p' : ℝ) := by exact_mod_cast Nat.le_max_left p 64
    have hplog' : Real.log (2 * (d : ℝ)) ≤ (p' : ℝ) := hplog.trans hpp'
    have hp'le : (p' : ℝ) ≤ 64 * (p : ℝ) := by
      exact_mod_cast (show p' ≤ 64 * p by omega)
    have hfn : (fun ω : SketchSample ζ b n =>
        spectralNorm (retainedCrossGram I V (mergeHeadSample I ω₀ ω))) =
        (fun ω => ‖SparseStack.crossGram I V (SparseStack.mergeHead I ω₀ ω)‖) := by
      funext ω
      rw [spectralNorm_eq_l2_opNorm, retainedCrossGram_eq_crossGram]
      rfl
    rw [hfn, uniformMeanReal_sketchSample_eq_expect hb0]
    have href := SparseStack.cross_gram_refined hζ hbζ I hI V hV hVsupp hd p' hp'64 hplog' ω₀
    set A₁ : ℝ := ((I.card : ℝ) + ((d : ℝ) + 2 * (p : ℝ) + 1)) / ((ζ * b : ℕ) : ℝ) +
      ((p : ℝ) + 1) / (ζ : ℝ) ^ 2
    set A₂ : ℝ := (I.card : ℝ) * (d : ℝ) / ((ζ : ℝ) ^ 2 * (b : ℝ) ^ 3) *
      (Nat.choose ζ 3 : ℝ)
    have hk : ((ζ * b : ℕ) : ℝ) = (ζ : ℝ) * (b : ℝ) := Nat.cast_mul ζ b
    have hN0 : (0 : ℝ) ≤ (I.card : ℝ) := Nat.cast_nonneg I.card
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hζ0 : (0 : ℝ) < (ζ : ℝ) := by exact_mod_cast hζ
    have hbR0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb0
    have h1a : 2 * ((I.card : ℝ) + ((d : ℝ) + 2 * (p' : ℝ) + 1)) / (3 * (b : ℝ) * (ζ : ℝ)) ≤
        64 * (((I.card : ℝ) + ((d : ℝ) + 2 * (p : ℝ) + 1)) / ((ζ * b : ℕ) : ℝ)) := by
      rw [hk, div_le_iff₀ (by positivity)]
      have heq : 64 * (((I.card : ℝ) + ((d : ℝ) + 2 * (p : ℝ) + 1)) / ((ζ : ℝ) * (b : ℝ))) *
          (3 * (b : ℝ) * (ζ : ℝ)) =
          192 * ((I.card : ℝ) + ((d : ℝ) + 2 * (p : ℝ) + 1)) := by
        field_simp
        ring
      rw [heq]
      linarith
    have h1b : ((p' : ℝ) + 1) / (ζ : ℝ) ^ 2 ≤ 64 * (((p : ℝ) + 1) / (ζ : ℝ) ^ 2) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hsq1 : Real.sqrt (2 * ((I.card : ℝ) + ((d : ℝ) + 2 * (p' : ℝ) + 1)) /
          (3 * (b : ℝ) * (ζ : ℝ)) + ((p' : ℝ) + 1) / (ζ : ℝ) ^ 2) ≤ 8 * Real.sqrt A₁ := by
      calc Real.sqrt (2 * ((I.card : ℝ) + ((d : ℝ) + 2 * (p' : ℝ) + 1)) /
            (3 * (b : ℝ) * (ζ : ℝ)) + ((p' : ℝ) + 1) / (ζ : ℝ) ^ 2)
          ≤ Real.sqrt (64 * A₁) := Real.sqrt_le_sqrt (by dsimp [A₁]; linarith)
        _ = 8 * Real.sqrt A₁ := by
            rw [Real.sqrt_mul (by norm_num), show (64 : ℝ) = 8 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
    have hA2_nonneg : 0 ≤ A₂ := by dsimp [A₂]; positivity
    have hsq2 : Real.sqrt (3 * (I.card : ℝ) * (d : ℝ) / ((ζ : ℝ) ^ 2 * (b : ℝ) ^ 3) *
          (Nat.choose ζ 3 : ℝ)) ≤ 2 * Real.sqrt A₂ := by
      calc Real.sqrt (3 * (I.card : ℝ) * (d : ℝ) / ((ζ : ℝ) ^ 2 * (b : ℝ) ^ 3) *
            (Nat.choose ζ 3 : ℝ))
          = Real.sqrt (3 * A₂) := by congr 1; dsimp [A₂]; ring
        _ ≤ Real.sqrt (4 * A₂) := Real.sqrt_le_sqrt (by linarith)
        _ = 2 * Real.sqrt A₂ := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
    have hrt1 : 0 ≤ Real.sqrt A₁ := Real.sqrt_nonneg A₁
    have hrt2 : 0 ≤ Real.sqrt A₂ := Real.sqrt_nonneg A₂
    linarith

/-- **Lemma 5.5 (High-moment bound for the full SparseStack Gram error, p. 28).** -/
theorem lemma_5_5_FullSketchMoment : Lemma_5_5_FullSketchMoment := by
  refine ⟨34, by norm_num, ?_⟩
  intro ζ b n D p hζ hb _hD hp U hU
  have hb0 : 0 < b := by omega
  have hfn : (fun ω : SketchSample ζ b n =>
      let A := (sparseStackOmega ω).transpose * U
      spectralNorm (A.transpose * A - 1) ^ (2 * p)) =
      (fun ω =>
        ‖(SparseStack.sketchMatrix ω * U).transpose *
          (SparseStack.sketchMatrix ω * U) - 1‖ ^ (2 * p)) := by
    funext ω
    dsimp only
    rw [spectralNorm_eq_l2_opNorm, sparseStackOmega_gram_eq]
  rw [hfn, uniformMeanReal_sketchSample_eq_expect hb0]
  have href := SparseStack.stack_moment hζ hb U hU p hp
  have hk : ((ζ * b : ℕ) : ℝ) = (b : ℝ) * (ζ : ℝ) := by push_cast; ring
  rw [hk]
  exact href

end Osi.UpperBound
