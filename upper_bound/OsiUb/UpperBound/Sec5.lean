import OsiUb.Spec
import OsiUb.Prelim.SubspaceSing
import SparseStack.IidNorm
import SparseStack.CrossGram
import SparseStack.External.StackMoment

/-!
# Section 5: Moments, Matrix Bernstein, Coupling, Convex Dominance, and Lemma 2.4

Proves all 9 statements belonging to Section 5 and Lemma 2.4:
* `fact_5_1_HeidaryOffDiagMoment` (`Fact_5_1_HeidaryOffDiagMoment`)
* `fact_5_2_ScalarVarMatrixBernstein` (`Fact_5_2_ScalarVarMatrixBernstein`)
* `lemma_5_3_IidOpNorm` (`Lemma_5_3_IidOpNorm`)
* `lemma_2_4_IsolatedCrossTerm` (`Lemma_2_4_IsolatedCrossTerm`)
* `lemma_2_4_IsolatedCrossTerm_Submatrix` (`Lemma_2_4_IsolatedCrossTerm_Submatrix`)
* `claim_5_4_SingleBlockCoupling` (`Claim_5_4_SingleBlockCoupling`)
* `lemma_5_5_CouplingJensen` (`Lemma_5_5_CouplingJensen`)
* `claim_5_6_SymmetricConvexDom` (`Claim_5_6_SymmetricConvexDom`)
* `lemma_5_7_FullSketchMoment` (`Lemma_5_7_FullSketchMoment`)
-/

namespace OsiUb.UpperBound

open OsiUb.Spec
open scoped BigOperators Matrix.Norms.L2Operator

/-! ## Section A: Shared Bridge Helpers -/

private lemma spectralNorm_eq_l2_opNorm {m l : Type} [Fintype m] [Fintype l] [DecidableEq l]
    (A : Matrix m l ℝ) : OsiUb.Spec.spectralNorm A = ‖A‖ :=
  OsiUb.Prelim.spectralNorm_eq_l2_opNorm A

private lemma signValue_eq_sparseStack (β : Bool) :
    OsiUb.Spec.signValue β = SparseStack.signValue β := by
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

private def mapOutcome {B : ℕ} (u : Fin (2 * B)) : SparseFock.EtaOutcome :=
  if u.val = 0 then .pos else if u.val = 1 then .neg else .zero

private lemma iidTernaryEntry_eq_yValue {B : ℕ} (u : Fin (2 * B)) :
    iidTernaryEntry u = SparseFock.SparseIIDCoupling.yValue (mapOutcome u) := by
  unfold iidTernaryEntry mapOutcome
  by_cases h0 : u.val = 0
  · simp [h0, SparseFock.SparseIIDCoupling.yValue]
  · by_cases h1 : u.val = 1
    · simp [h1, SparseFock.SparseIIDCoupling.yValue]
    · simp [h0, h1, SparseFock.SparseIIDCoupling.yValue]

private lemma iidTernaryEntry_eq_eta_div_sqrt {B : ℕ} (hB : 1 ≤ B) (u : Fin (2 * B)) :
    iidTernaryEntry u = SparseFock.TernaryJacobi.eta B (mapOutcome u) / Real.sqrt (B : ℝ) := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hsqrt : Real.sqrt (B : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hBpos).ne'
  unfold iidTernaryEntry mapOutcome
  by_cases h0 : u.val = 0
  · simp [h0, SparseFock.TernaryJacobi.eta, div_self hsqrt]
  · by_cases h1 : u.val = 1
    · simp [h1, SparseFock.TernaryJacobi.eta, neg_div, div_self hsqrt]
    · simp [h0, h1, SparseFock.TernaryJacobi.eta]

private lemma iidTernaryMatrix_eq_iidMatrix {m n B : ℕ} (hB : 1 ≤ B)
    (ω : IidTernarySample m n B) :
    iidTernaryMatrix ω = SparseStack.iidMatrix B (fun p => mapOutcome (ω p.1 p.2)) := by
  ext ℓ j
  exact iidTernaryEntry_eq_eta_div_sqrt hB (ω ℓ j)

private lemma sum_mapOutcome_indicator {B : ℕ} (hB : 1 ≤ B) (y : SparseFock.EtaOutcome) :
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

/-- Generic pushforward of uniform sampling on `κ → Fin (2 * B)` under `mapOutcome` to
`independentProduct (fun _ : κ => coordinateLaw B _)`. -/
private lemma uniformMeanReal_mapOutcome_eq_expect {κ : Type} [Fintype κ] [DecidableEq κ]
    {B : ℕ} (hB : 1 ≤ B) (hb0 : 0 < B)
    (G : (κ → SparseFock.EtaOutcome) → ℝ) :
    uniformMeanReal (κ → Fin (2 * B)) (fun x => G (fun k => mapOutcome (x k))) =
      (SparseFock.FiniteLaw.independentProduct
        (fun _ : κ => SparseFock.SparseIIDCoupling.coordinateLaw B hb0)).expect G := by
  have hcard : Fintype.card (κ → Fin (2 * B)) = (2 * B) ^ Fintype.card κ := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hinv : (Fintype.card (κ → Fin (2 * B)) : ℝ)⁻¹ =
      ∏ _k : κ, (2 * (B : ℝ))⁻¹ := by
    rw [hcard, Finset.prod_const, Finset.card_univ]
    push_cast
    rw [← inv_pow]
  have hdecomp : ∀ y : κ → SparseFock.EtaOutcome,
      G y = ∑ z : κ → SparseFock.EtaOutcome,
        (∏ k : κ, if y k = z k then (1 : ℝ) else 0) * G z := by
    intro y
    rw [Fintype.sum_eq_single y]
    · simp
    · intro z hzy
      have hex : ∃ k, y k ≠ z k := by
        by_contra hall
        push Not at hall
        exact hzy (funext hall).symm
      obtain ⟨k, hk⟩ := hex
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk), zero_mul]
  rw [uniformMeanReal, hinv, Finset.mul_sum]
  have hexpand : ∀ x : κ → Fin (2 * B),
      (∏ _k : κ, (2 * (B : ℝ))⁻¹) * G (fun k => mapOutcome (x k)) =
        ∑ z : κ → SparseFock.EtaOutcome,
          (∏ k : κ, (2 * (B : ℝ))⁻¹ * (if mapOutcome (x k) = z k then (1 : ℝ) else 0)) * G z := by
    intro x
    rw [hdecomp (fun k => mapOutcome (x k)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← mul_assoc, ← Finset.prod_mul_distrib]
  simp_rw [hexpand]
  rw [Finset.sum_comm, SparseFock.FiniteLaw.expect]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [← Fintype.prod_sum (fun (k : κ) (u : Fin (2 * B)) =>
    (2 * (B : ℝ))⁻¹ * (if mapOutcome u = z k then (1 : ℝ) else 0))]
  rw [SparseFock.FiniteLaw.independentProduct_weight]
  refine Finset.prod_congr rfl fun k _ => ?_
  exact sum_mapOutcome_indicator hB (z k)

private lemma uniformMeanReal_iidTernarySample_eq_expect {m n B : ℕ} (hB : 2 ≤ B) (hB1 : 1 < B)
    (G : SparseFock.ProductFock.Configuration m n → ℝ) :
    uniformMeanReal (IidTernarySample m n B) (fun ω => G (fun p => mapOutcome (ω p.1 p.2))) =
      (SparseFock.ProductFock.iidLaw B hB1 m n).expect G := by
  have h1 : uniformMeanReal (IidTernarySample m n B)
      (fun ω => G (fun p => mapOutcome (ω p.1 p.2))) =
      uniformMeanReal (Fin m × Fin n → Fin (2 * B))
        (fun x => G (fun p => mapOutcome (x p))) := by
    unfold uniformMeanReal
    rw [Fintype.card_congr (Equiv.curry (Fin m) (Fin n) (Fin (2 * B))).symm,
      ← (Equiv.curry (Fin m) (Fin n) (Fin (2 * B))).sum_comp
        (fun ω => G (fun p => mapOutcome (ω p.1 p.2)))]
    rfl
  rw [h1, uniformMeanReal_mapOutcome_eq_expect (by omega) (by omega) G]
  rfl

/-! ## Section B: Fact 5.1 (Heidary Off-Diagonal `2p`-th Moment) -/

private lemma iidOffDiagGram_eq_iidGramError {a B n d : ℕ} (ha : 1 ≤ a) (hB : 2 ≤ B)
    (W : Matrix (Fin n) (Fin d) ℝ) (hW : W.transpose * W = 1)
    (ω : IidTernarySample (a * B) n B) :
    iidOffDiagGram a B n d W ω =
      SparseFock.VacuumMoment.iidGramError B (SparseFock.MatrixFrameBridge.frameOfMatrix W hW)
        (fun s => mapOutcome (ω s.1 s.2)) := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
  have hsq : Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) = (B : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg B)
  have hm : (1 : ℝ) / (((a * B : ℕ) : ℝ)) = (a : ℝ)⁻¹ * (1 / (B : ℝ)) := by
    push_cast
    field_simp
  ext α γ
  rw [SparseFock.VacuumMoment.iidGramError_apply, hm]
  simp only [iidOffDiagGram, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, SparseFock.MatrixFrameBridge.frameOfMatrix_u,
    SparseFock.ProductFock.etaCoordinate, iidTernaryMatrix,
    iidTernaryEntry_eq_eta_div_sqrt (by omega : 1 ≤ B)]
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [div_mul_div_comm, hsq]
  ring

/-- **Fact 5.1 (Heidary `[Hei26]` off-diagonal `2p`-th trace moment bound, p. 30, Eq. (27)).** -/
theorem fact_5_1_HeidaryOffDiagMoment : Fact_5_1_HeidaryOffDiagMoment := by
  intro a B n d p hB ha _hd _hp W hW
  have hW' : W.transpose * W = 1 := hW
  have hB1 : 1 < B := by omega
  have ha0 : 0 < a := by omega
  let G : SparseFock.ProductFock.Configuration (a * B) n → ℝ :=
    fun cfg => ((SparseFock.VacuumMoment.iidGramError B
      (SparseFock.MatrixFrameBridge.frameOfMatrix W hW') cfg) ^ (2 * p)).trace
  have hfn : (fun ω : IidTernarySample (a * B) n B =>
      ((iidOffDiagGram a B n d W ω) ^ (2 * p)).trace) =
      (fun ω => G (fun s => mapOutcome (ω s.1 s.2))) := by
    funext ω
    dsimp only [G]
    rw [iidOffDiagGram_eq_iidGramError ha hB W hW' ω]
  rw [hfn, uniformMeanReal_iidTernarySample_eq_expect hB hB1 G]
  have href := SparseStack.External.heidary_eq83_all_q (s := a) (b := B) (q := p) ha0 hB1
    (SparseFock.MatrixFrameBridge.frameOfMatrix W hW')
  rw [SparseStack.External.betaEnvelope_eq] at href
  have hcast1 : ((d + 2 * p + 1 : ℕ) : ℝ) = (d : ℝ) + 2 * (p : ℝ) + 1 := by push_cast; ring
  have hcast2 : ((2 * p + 1 : ℕ) : ℝ) = 2 * (p : ℝ) + 1 := by push_cast; ring
  rw [hcast1, hcast2, ← mul_assoc (3 : ℝ)] at href
  exact href

/-! ## Section C: Fact 5.2 (Scalar-Variance Matrix Bernstein Bound) -/

/-- Scalar Bernstein exponential inequality via elementary calculus (no infinite series):
for all `u < 3` and `c_b ∈ [0, 1)` with `u ≤ 3 * c_b`,
`exp u ≤ 1 + u + (u² / 2) / (1 - c_b)`. -/
private lemma exp_le_bernstein_quad {u c_b : ℝ} (hc0 : 0 ≤ c_b) (hc1 : c_b < 1)
    (huc : u ≤ 3 * c_b) :
    Real.exp u ≤ 1 + u + (u ^ 2 / 2) / (1 - c_b) := by
  have h1c : 0 < 1 - c_b := by linarith
  -- `g(x) = exp x - (1 + x + x²/2)` has derivative `exp x - (1 + x) ≥ 0` on all of `ℝ`
  let g : ℝ → ℝ := fun x => Real.exp x - (1 + x + x ^ 2 / 2)
  have hg_deriv : ∀ x : ℝ, HasDerivAt g (Real.exp x - (1 + x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => 1 + y + y ^ 2 / 2) (1 + x) x := by
      have hp : HasDerivAt (fun y : ℝ => y ^ 2 / 2) (2 * x ^ (2 - 1) * 1 / 2) x :=
        ((hasDerivAt_id x).pow 2).div_const 2
      have hlin : HasDerivAt (fun y : ℝ => 1 + y) (0 + 1) x :=
        (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
      exact (hlin.add hp).congr_deriv (by norm_num)
    exact (Real.hasDerivAt_exp x).sub h1
  have hg_diff : Differentiable ℝ g := fun x => (hg_deriv x).differentiableAt
  have hg_mono : ∀ x y : ℝ, x ≤ y → g x ≤ g y := by
    intro x y hxy
    have h := mul_sub_le_image_sub_of_le_deriv hg_diff (C := 0) (fun z => by
      rw [(hg_deriv z).deriv]
      linarith [Real.add_one_le_exp z]) hxy
    linarith
  have hg0 : g 0 = 0 := by simp [g]
  rcases le_total u 0 with hu0 | hu0
  · have hgu : Real.exp u ≤ 1 + u + u ^ 2 / 2 := by
      have h := hg_mono u 0 hu0
      rw [hg0] at h
      dsimp only [g] at h
      linarith
    have hquad_le : u ^ 2 / 2 ≤ (u ^ 2 / 2) / (1 - c_b) := by
      rw [le_div_iff₀ h1c]
      have hsq : 0 ≤ u ^ 2 / 2 := by positivity
      nlinarith
    linarith
  · -- For `u ≥ 0`: `q(x) = (1 + (2/3) x + x²/6) exp(-x) - (1 - x/3)` has `q(0) = 0` and
    -- `q'(x) = (1/3) (1 - (1 + x + x²/2) exp(-x)) ≥ 0` on `[0, ∞)` since `1 + x + x²/2 ≤ exp x`
    let q : ℝ → ℝ := fun x => (1 + 2 / 3 * x + x ^ 2 / 6) * Real.exp (-x) - (1 - x / 3)
    have hq_deriv : ∀ x : ℝ,
        HasDerivAt q ((1 / 3 : ℝ) * (1 - (1 + x + x ^ 2 / 2) * Real.exp (-x))) x := by
      intro x
      have hp1 : HasDerivAt (fun y : ℝ => 1 + 2 / 3 * y + y ^ 2 / 6) (2 / 3 + x / 3) x := by
        have ha : HasDerivAt (fun y : ℝ => 1 + 2 / 3 * y) (0 + 2 / 3 * 1) x :=
          (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).const_mul (2 / 3))
        have hb : HasDerivAt (fun y : ℝ => y ^ 2 / 6) (2 * x ^ (2 - 1) * 1 / 6) x :=
          ((hasDerivAt_id x).pow 2).div_const 6
        exact (ha.add hb).congr_deriv (by norm_num; ring)
      have hp2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-x) * (-1)) x :=
        (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg
      have hp3 : HasDerivAt (fun y : ℝ => 1 - y / 3) (0 - 1 / 3) x :=
        (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).div_const 3)
      exact ((hp1.mul hp2).sub hp3).congr_deriv (by norm_num; ring)
    have hq_diff : Differentiable ℝ q := fun x => (hq_deriv x).differentiableAt
    have hq_nonneg : 0 ≤ q u := by
      have h := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
        hq_diff.continuous.continuousOn hq_diff.differentiableOn (C := 0)
        (fun z hz => by
          rw [(hq_deriv z).deriv]
          have hz0 : 0 ≤ z := interior_subset hz
          have hgz : 1 + z + z ^ 2 / 2 ≤ Real.exp z := by
            have hm := hg_mono 0 z hz0
            rw [hg0] at hm
            dsimp only [g] at hm
            linarith
          have hprod : (1 + z + z ^ 2 / 2) * Real.exp (-z) ≤ 1 := by
            calc (1 + z + z ^ 2 / 2) * Real.exp (-z)
                ≤ Real.exp z * Real.exp (-z) :=
                  mul_le_mul_of_nonneg_right hgz (Real.exp_pos _).le
              _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
          linarith)
        0 (Set.mem_Ici.mpr le_rfl) u hu0 hu0
      have hq0 : q 0 = 0 := by simp [q]
      linarith
    have hexp_mul : (1 - u / 3) * Real.exp u ≤ 1 + 2 / 3 * u + u ^ 2 / 6 := by
      have hmul := mul_le_mul_of_nonneg_right hq_nonneg (Real.exp_pos u).le
      dsimp only [q] at hmul
      rw [zero_mul, sub_mul, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        mul_one] at hmul
      linarith
    have h1u3 : 0 < 1 - u / 3 := by linarith
    have hdiv_u : Real.exp u ≤ 1 + u + (u ^ 2 / 2) / (1 - u / 3) := by
      have hcalc : (1 - u / 3) * Real.exp u ≤ (1 + u) * (1 - u / 3) + u ^ 2 / 2 := by
        linarith
      have hrew : 1 + u + (u ^ 2 / 2) / (1 - u / 3) =
          ((1 + u) * (1 - u / 3) + u ^ 2 / 2) / (1 - u / 3) := by
        rw [add_div, mul_div_cancel_right₀ _ h1u3.ne']
      rw [hrew, le_div_iff₀ h1u3]
      linarith
    have hdiv_mono : (u ^ 2 / 2) / (1 - u / 3) ≤ (u ^ 2 / 2) / (1 - c_b) :=
      div_le_div_of_nonneg_left (by positivity) h1c (by linarith)
    linarith

private lemma smul_conj_diagonal {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (c : ℝ) :
    c • (U * Matrix.diagonal lam * star U) =
      U * Matrix.diagonal (fun i => c * lam i) * star U := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases hlk : l = k
  · subst hlk
    simp only [Matrix.diagonal_apply_eq]
    ring
  · simp only [Matrix.diagonal_apply_ne _ hlk, mul_zero, zero_mul]

/-- Spectral trace inequality for a Hermitian matrix `A` with `‖A‖ ≤ ℓ` and `0 < θ`, `θ * ℓ < 3`:
for any PSD matrix `M`,
`tr(M exp(θ A)) ≤ tr M + θ tr(M A) + ((θ² / 2) / (1 - θ ℓ / 3)) tr(M A²)`. -/
private lemma trace_mul_exp_bernstein {d : ℕ} (M A : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.PosSemidef) (hA : A.IsHermitian) {θ ℓ : ℝ} (hθ : 0 < θ) (hℓ0 : 0 ≤ ℓ)
    (hθℓ : θ * ℓ < 3) (hAnorm : ‖A‖ ≤ ℓ) :
    (M * NormedSpace.exp (θ • A)).trace ≤
      M.trace + θ * (M * A).trace +
        ((θ ^ 2 / 2) / (1 - θ * ℓ / 3)) * (M * A ^ 2).trace := by
  set U : Matrix (Fin d) (Fin d) ℝ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  set lam : Fin d → ℝ := hA.eigenvalues
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hB : (star U * M * U).PosSemidef := by
    rw [Matrix.star_eq_conjTranspose]
    exact hM.conjTranspose_mul_mul_same _
  have hθA_eq : θ • A = U * Matrix.diagonal (fun i => θ * lam i) * star U := by
    conv_lhs => rw [SparseStack.MatrixConc.spectral_eq A hA]
    exact smul_conj_diagonal U lam θ
  have hA2_eq : A ^ 2 = U * Matrix.diagonal (fun i => (lam i) ^ 2) * star U := by
    rw [sq]
    conv_lhs =>
      rw [SparseStack.MatrixConc.spectral_eq A hA]
    have hmid : (U * Matrix.diagonal lam * star U) * (U * Matrix.diagonal lam * star U) =
        U * (Matrix.diagonal lam * (star U * U) * Matrix.diagonal lam) * star U := by
      simp only [mul_assoc]
    rw [hmid, hUU, mul_one, Matrix.diagonal_mul_diagonal]
    simp only [sq]
  have t_exp : (M * NormedSpace.exp (θ • A)).trace =
      ∑ i : Fin d, (star U * M * U) i i * Real.exp (θ * lam i) := by
    rw [hθA_eq, SparseStack.MatrixConc.exp_conj_diagonal U hUU,
      SparseStack.MatrixConc.trace_mul_conj_diagonal]
  have t_one : M.trace = ∑ i : Fin d, (star U * M * U) i i * 1 := by
    rw [← SparseStack.MatrixConc.trace_mul_conj_diagonal, Matrix.diagonal_one, mul_one,
      Unitary.mul_star_self_of_mem (SetLike.coe_mem _), mul_one]
  have t_lin : (M * A).trace = ∑ i : Fin d, (star U * M * U) i i * lam i := by
    conv_lhs => rw [SparseStack.MatrixConc.spectral_eq A hA]
    exact SparseStack.MatrixConc.trace_mul_conj_diagonal M U lam
  have t_sq : (M * A ^ 2).trace = ∑ i : Fin d, (star U * M * U) i i * (lam i) ^ 2 := by
    rw [hA2_eq, SparseStack.MatrixConc.trace_mul_conj_diagonal]
  rw [t_exp, t_one, t_lin, t_sq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hdiag0 : 0 ≤ (star U * M * U) i i := hB.diag_nonneg
  have hlam_le : |lam i| ≤ ℓ := by
    have hnorm_eq := SparseStack.MatrixConc.l2_opNorm_eq_norm_eigenvalues A hA
    have hpi : ‖lam i‖ ≤ ‖lam‖ := norm_le_pi_norm lam i
    rw [Real.norm_eq_abs] at hpi
    linarith
  have hu_le : θ * lam i ≤ 3 * (θ * ℓ / 3) := by
    have h1 : lam i ≤ ℓ := (le_abs_self (lam i)).trans hlam_le
    have h2 : θ * lam i ≤ θ * ℓ := mul_le_mul_of_nonneg_left h1 hθ.le
    linarith
  have hexp_i := exp_le_bernstein_quad (c_b := θ * ℓ / 3) (by positivity) (by linarith) hu_le
  have hrewrite : 1 + θ * lam i + ((θ * lam i) ^ 2 / 2) / (1 - θ * ℓ / 3) =
      1 + θ * lam i + ((θ ^ 2 / 2) / (1 - θ * ℓ / 3)) * (lam i) ^ 2 := by
    ring
  rw [hrewrite] at hexp_i
  have hmul := mul_le_mul_of_nonneg_left hexp_i hdiag0
  linarith

/-- For `M ⪰ 0` and `K ⪰ 0`, `0 ≤ tr(M K)`. -/
private lemma trace_mul_nonneg_of_posSemidef {d : ℕ} {M K : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosSemidef) (hK : K.PosSemidef) :
    0 ≤ (M * K).trace := by
  have hKh := hK.isHermitian
  set V : Matrix (Fin d) (Fin d) ℝ := (hKh.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have hB : (star V * M * V).PosSemidef := by
    rw [Matrix.star_eq_conjTranspose]
    exact hM.conjTranspose_mul_mul_same _
  conv_rhs => rw [SparseStack.MatrixConc.spectral_eq K hKh]
  rw [SparseStack.MatrixConc.trace_mul_conj_diagonal]
  exact Finset.sum_nonneg fun i _ => mul_nonneg hB.diag_nonneg (hK.eigenvalues_nonneg i)

/-- One Bernstein MGF step on a finite law `ν`. -/
private lemma bernstein_step {Ω : Type} [Fintype Ω] {d : ℕ} (ν : SparseFock.FiniteLaw Ω)
    (P_mat : Ω → Matrix (Fin d) (Fin d) ℝ) {θ ℓ v_j : ℝ}
    (hθ : 0 < θ) (hℓ0 : 0 ≤ ℓ) (hθℓ : θ * ℓ < 3)
    (hHerm : ∀ ω, (P_mat ω).IsHermitian)
    (hMean : ∑ ω, ν.weight ω • P_mat ω = 0)
    (hNorm : ∀ ω, ‖P_mat ω‖ ≤ ℓ)
    (hVar : (v_j • (1 : Matrix (Fin d) (Fin d) ℝ) -
      ∑ ω, ν.weight ω • (P_mat ω) ^ 2).PosSemidef)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosSemidef) :
    ∑ ω, ν.weight ω * (M * NormedSpace.exp (θ • P_mat ω)).trace ≤
      Real.exp (((θ ^ 2 / 2) / (1 - θ * ℓ / 3)) * v_j) * M.trace := by
  set c_θ : ℝ := (θ ^ 2 / 2) / (1 - θ * ℓ / 3)
  have hc_θ0 : 0 ≤ c_θ := by
    have : 0 < 1 - θ * ℓ / 3 := by linarith
    positivity
  have hpt : ∀ ω, ν.weight ω * (M * NormedSpace.exp (θ • P_mat ω)).trace ≤
      ν.weight ω * (M.trace + θ * (M * P_mat ω).trace + c_θ * (M * (P_mat ω) ^ 2).trace) :=
    fun ω => mul_le_mul_of_nonneg_left
      (trace_mul_exp_bernstein M (P_mat ω) hM (hHerm ω) hθ hℓ0 hθℓ (hNorm ω))
      (ν.weight_nonneg ω)
  have hlin1 : ∑ ω, ν.weight ω * (M * P_mat ω).trace = 0 := by
    have h : (M * ∑ ω, ν.weight ω • P_mat ω).trace = 0 := by
      rw [hMean, mul_zero, Matrix.trace_zero]
    rw [Matrix.mul_sum, Matrix.trace_sum] at h
    simpa only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] using h
  have hlin2 : ∑ ω, ν.weight ω * (M * (P_mat ω) ^ 2).trace ≤ v_j * M.trace := by
    have hnonneg := trace_mul_nonneg_of_posSemidef hM hVar
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, mul_one, Matrix.trace_smul,
      smul_eq_mul, Matrix.mul_sum, Matrix.trace_sum] at hnonneg
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at hnonneg
    linarith
  calc ∑ ω, ν.weight ω * (M * NormedSpace.exp (θ • P_mat ω)).trace
      ≤ ∑ ω, ν.weight ω *
          (M.trace + θ * (M * P_mat ω).trace + c_θ * (M * (P_mat ω) ^ 2).trace) :=
        Finset.sum_le_sum fun ω _ => hpt ω
    _ = (∑ ω, ν.weight ω) * M.trace + θ * (∑ ω, ν.weight ω * (M * P_mat ω).trace) +
          c_θ * (∑ ω, ν.weight ω * (M * (P_mat ω) ^ 2).trace) := by
        rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ω _ => ?_
        ring
    _ ≤ 1 * M.trace + θ * 0 + c_θ * (v_j * M.trace) := by
        rw [ν.sum_weight, hlin1]
        nlinarith
    _ = (1 + c_θ * v_j) * M.trace := by ring
    _ ≤ Real.exp (c_θ * v_j) * M.trace :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (c_θ * v_j)])
          hM.trace_nonneg

/-- Golden–Thompson MGF iteration across independent matrix summands. -/
private lemma bernstein_iteration {m d : ℕ} {Ω : Type} [Fintype Ω]
    (μ : Fin m → SparseFock.FiniteLaw Ω)
    (P_mat : Fin m → Ω → Matrix (Fin d) (Fin d) ℝ)
    (v_coord : Fin m → ℝ) {θ ℓ : ℝ}
    (hθ : 0 < θ) (hℓ0 : 0 ≤ ℓ) (hθℓ : θ * ℓ < 3)
    (hHerm : ∀ j ω, (P_mat j ω).IsHermitian)
    (hMean : ∀ j, ∑ ω, (μ j).weight ω • P_mat j ω = 0)
    (hNorm : ∀ j ω, ‖P_mat j ω‖ ≤ ℓ)
    (hVar : ∀ j, (v_coord j • (1 : Matrix (Fin d) (Fin d) ℝ) -
      ∑ ω, (μ j).weight ω • (P_mat j ω) ^ 2).PosSemidef)
    (s : Finset (Fin m)) :
    (SparseFock.FiniteLaw.independentProduct μ).expect
        (fun y => (NormedSpace.exp (θ • ∑ j ∈ s, P_mat j (y j))).trace) ≤
      (d : ℝ) * Real.exp (((θ ^ 2 / 2) / (1 - θ * ℓ / 3)) * ∑ j ∈ s, v_coord j) := by
  set c_θ : ℝ := (θ ^ 2 / 2) / (1 - θ * ℓ / 3)
  induction s using Finset.induction_on with
  | empty =>
    simp [Matrix.trace_one]
  | insert a s ha ih =>
    have hpt : ∀ y : Fin m → Ω,
        ∑ ω, (μ a).weight ω *
            (NormedSpace.exp (θ • ∑ j ∈ insert a s, P_mat j (Function.update y a ω j))).trace ≤
          Real.exp (c_θ * v_coord a) *
            (NormedSpace.exp (θ • ∑ j ∈ s, P_mat j (y j))).trace := by
      intro y
      have hupd : ∀ ω, θ • ∑ j ∈ insert a s, P_mat j (Function.update y a ω j) =
          (θ • ∑ j ∈ s, P_mat j (y j)) + θ • P_mat a ω := by
        intro ω
        rw [Finset.sum_insert ha, Function.update_self, smul_add, add_comm (θ • P_mat a ω)]
        congr 2
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Function.update_of_ne (by rintro rfl; exact ha hj)]
      have hHs : (θ • ∑ j ∈ s, P_mat j (y j)).IsHermitian := by
        rw [Finset.smul_sum]
        exact Matrix.isHermitian_iff_isSymm.mpr <| by
          rw [Matrix.IsSymm, Matrix.transpose_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.transpose_smul, Matrix.isHermitian_iff_isSymm.mp (hHerm j (y j))]
      have hM : (NormedSpace.exp (θ • ∑ j ∈ s, P_mat j (y j))).PosSemidef :=
        SparseStack.MatrixConc.posSemidef_exp _ hHs
      calc ∑ ω, (μ a).weight ω *
            (NormedSpace.exp (θ • ∑ j ∈ insert a s, P_mat j (Function.update y a ω j))).trace
          ≤ ∑ ω, (μ a).weight ω *
              (NormedSpace.exp (θ • ∑ j ∈ s, P_mat j (y j)) *
                NormedSpace.exp (θ • P_mat a ω)).trace := by
            refine Finset.sum_le_sum fun ω _ => ?_
            rw [hupd ω]
            have hHa : (θ • P_mat a ω).IsHermitian :=
              Matrix.isHermitian_iff_isSymm.mpr <| by
                rw [Matrix.IsSymm, Matrix.transpose_smul,
                  Matrix.isHermitian_iff_isSymm.mp (hHerm a ω)]
            exact mul_le_mul_of_nonneg_left
              (SparseStack.golden_thompson _ _ hHs hHa) ((μ a).weight_nonneg ω)
        _ ≤ Real.exp (c_θ * v_coord a) *
              (NormedSpace.exp (θ • ∑ j ∈ s, P_mat j (y j))).trace :=
            bernstein_step (μ a) (P_mat a) hθ hℓ0 hθℓ (hHerm a) (hMean a) (hNorm a) (hVar a)
              _ hM
    calc (SparseFock.FiniteLaw.independentProduct μ).expect
          (fun y => (NormedSpace.exp (θ • ∑ j ∈ insert a s, P_mat j (y j))).trace)
        = (SparseFock.FiniteLaw.independentProduct μ).expect
            (fun y => ∑ ω, (μ a).weight ω *
              (NormedSpace.exp (θ • ∑ j ∈ insert a s, P_mat j (Function.update y a ω j))).trace) :=
          SparseStack.MatrixConc.expect_resample μ a _
      _ ≤ (SparseFock.FiniteLaw.independentProduct μ).expect
            (fun y => Real.exp (c_θ * v_coord a) *
              (NormedSpace.exp (θ • ∑ j ∈ s, P_mat j (y j))).trace) :=
          SparseFock.FiniteLaw.expect_mono _ hpt
      _ = Real.exp (c_θ * v_coord a) *
            (SparseFock.FiniteLaw.independentProduct μ).expect
              (fun y => (NormedSpace.exp (θ • ∑ j ∈ s, P_mat j (y j))).trace) :=
          SparseFock.FiniteLaw.expect_smul _ _ _
      _ ≤ Real.exp (c_θ * v_coord a) * ((d : ℝ) * Real.exp (c_θ * ∑ j ∈ s, v_coord j)) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = (d : ℝ) * Real.exp (c_θ * ∑ j ∈ insert a s, v_coord j) := by
          rw [Finset.sum_insert ha, mul_add, Real.exp_add]
          ring

/-- Two-sided trace exponential bound for any Hermitian matrix `S` (`d ≥ 1`, `θ ≥ 0`):
`exp(θ ‖S‖) ≤ tr exp(θ S) + tr exp(-θ S)`. -/
private lemma exp_norm_le_two_sided_trace_exp {d : ℕ} (hd : 1 ≤ d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) {θ : ℝ} (_hθ : 0 ≤ θ) :
    Real.exp (θ * ‖S‖) ≤
      (NormedSpace.exp (θ • S)).trace + (NormedSpace.exp ((-θ) • S)).trace := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set U : Matrix (Fin d) (Fin d) ℝ := (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  set lam : Fin d → ℝ := hS.eigenvalues
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have htr_pos : (NormedSpace.exp (θ • S)).trace = ∑ i : Fin d, Real.exp (θ * lam i) := by
    have h1 : θ • S = U * Matrix.diagonal (fun i => θ * lam i) * star U := by
      conv_lhs => rw [SparseStack.MatrixConc.spectral_eq S hS]
      exact smul_conj_diagonal U lam θ
    rw [h1, SparseStack.MatrixConc.exp_conj_diagonal U hUU, Matrix.trace_mul_cycle, hUU,
      one_mul, Matrix.trace_diagonal]
  have htr_neg : (NormedSpace.exp ((-θ) • S)).trace = ∑ i : Fin d, Real.exp ((-θ) * lam i) := by
    have h1 : (-θ) • S = U * Matrix.diagonal (fun i => (-θ) * lam i) * star U := by
      conv_lhs => rw [SparseStack.MatrixConc.spectral_eq S hS]
      exact smul_conj_diagonal U lam (-θ)
    rw [h1, SparseStack.MatrixConc.exp_conj_diagonal U hUU, Matrix.trace_mul_cycle, hUU,
      one_mul, Matrix.trace_diagonal]
  rw [SparseStack.MatrixConc.l2_opNorm_eq_norm_eigenvalues S hS, htr_pos, htr_neg]
  obtain ⟨i₀, hi₀⟩ := (IsGreatest.pi_norm lam).1
  dsimp only at hi₀
  rw [← hi₀, Real.norm_eq_abs]
  have hsum_pos0 : 0 ≤ ∑ i : Fin d, Real.exp (θ * lam i) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hsum_neg0 : 0 ≤ ∑ i : Fin d, Real.exp ((-θ) * lam i) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  rcases le_total 0 (lam i₀) with h0 | h0
  · rw [abs_of_nonneg h0]
    have hsingle := Finset.single_le_sum (fun i _ => (Real.exp_pos (θ * lam i)).le)
      (Finset.mem_univ i₀)
    linarith
  · rw [abs_of_nonpos h0, show θ * -lam i₀ = (-θ) * lam i₀ by ring]
    have hsingle := Finset.single_le_sum (fun i _ => (Real.exp_pos ((-θ) * lam i)).le)
      (Finset.mem_univ i₀)
    linarith

/-- **Fact 5.2 (Matrix Bernstein expectation bound, pp. 30–31, Eq. (28)).** -/
theorem fact_5_2_ScalarVarMatrixBernstein : Fact_5_2_ScalarVarMatrixBernstein := by
  classical
  intro m d hd α _ pmf hpmf R v_coord v ℓ hℓ0 hv_coord0 hv_sum hHerm hMean hNorm hVar
  have hv0 : 0 ≤ v := (Finset.sum_nonneg fun j _ => hv_coord0 j).trans hv_sum
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h2d_gt1 : (1 : ℝ) < 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  set L : ℝ := Real.log (2 * (d : ℝ))
  have hL_pos : 0 < L := Real.log_pos h2d_gt1
  -- Push forward heterogeneous coordinates to `U := Σ k : Fin m, α k`
  let μ : Fin m → SparseFock.FiniteLaw (Σ k : Fin m, α k) := fun j =>
    { weight := fun u => if h : u.1 = j then pmf j (h ▸ u.2) else 0
      weight_nonneg := fun u => by
        by_cases h : u.1 = j
        · simp only [dif_pos h]
          exact hpmf.1 j _
        · simp [dif_neg h]
      sum_weight := by
        rw [Fintype.sum_sigma, Finset.sum_eq_single j]
        · exact (Finset.sum_congr rfl fun a _ => dif_pos rfl).trans (hpmf.2 j)
        · intro k _ hkj
          exact Finset.sum_eq_zero fun a _ => by simp [dif_neg hkj]
        · intro hj
          exact absurd (Finset.mem_univ j) hj }
  let P_mat : Fin m → (Σ k : Fin m, α k) → Matrix (Fin d) (Fin d) ℝ :=
    fun j u => if h : u.1 = j then R j (h ▸ u.2) else 0
  have hP_sum : ∀ (j : Fin m) (g : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ),
      g 0 = 0 →
      (∑ u : (Σ k : Fin m, α k), (μ j).weight u • g (P_mat j u)) =
        ∑ a : α j, pmf j a • g (R j a) := by
    intro j g hg0
    rw [Fintype.sum_sigma, Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp [μ, P_mat]
    · intro k _ hkj
      refine Finset.sum_eq_zero fun a _ => ?_
      simp [μ, P_mat, dif_neg hkj, hg0]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hP_herm : ∀ j u, (P_mat j u).IsHermitian := by
    intro j u
    by_cases h : u.1 = j
    · simp only [P_mat, dif_pos h]
      exact hHerm j _
    · simp [P_mat, dif_neg h]
  have hP_mean : ∀ j, ∑ u, (μ j).weight u • P_mat j u = 0 := by
    intro j
    rw [hP_sum j (fun M => M) rfl]
    exact hMean j
  have hP_norm : ∀ j u, ‖P_mat j u‖ ≤ ℓ := by
    intro j u
    by_cases h : u.1 = j
    · simp only [P_mat, dif_pos h, ← spectralNorm_eq_l2_opNorm]
      exact hNorm j _
    · simp [P_mat, dif_neg h, hℓ0]
  have hP_var : ∀ j, (v_coord j • (1 : Matrix (Fin d) (Fin d) ℝ) -
      ∑ u, (μ j).weight u • (P_mat j u) ^ 2).PosSemidef := by
    intro j
    rw [hP_sum j (fun M => M ^ 2) (by simp)]
    exact hVar j
  -- Relate `prodExpectReal` to `(independentProduct μ).expect`
  let P_law := SparseFock.FiniteLaw.independentProduct μ
  set E_val : ℝ := prodExpectReal pmf (fun x => spectralNorm (∑ j : Fin m, R j (x j)))
  have hE_eq : E_val = P_law.expect (fun y => ‖∑ j : Fin m, P_mat j (y j)‖) := by
    let emb : (∀ j : Fin m, α j) → (Fin m → Σ k : Fin m, α k) := fun x j => ⟨j, x j⟩
    have hemb_inj : Function.Injective emb := by
      intro x₁ x₂ heq
      funext j
      simpa only [emb, Sigma.mk.inj_iff, heq_eq_eq, true_and] using congr_fun heq j
    rw [SparseFock.FiniteLaw.expect]
    have hsub : (∑ y : (Fin m → Σ k : Fin m, α k),
        P_law.weight y * ‖∑ j : Fin m, P_mat j (y j)‖) =
        ∑ y ∈ Finset.univ.image emb,
          P_law.weight y * ‖∑ j : Fin m, P_mat j (y j)‖ := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro y _ hy_not
      have hnot_all : ¬ ∀ j : Fin m, (y j).1 = j := by
        intro hall
        apply hy_not
        rw [Finset.mem_image]
        refine ⟨fun j => (hall j) ▸ (y j).2, Finset.mem_univ _, ?_⟩
        funext j
        have hmk : ∀ (p : Σ k : Fin m, α k) (hp : p.1 = j),
            (⟨j, hp ▸ p.2⟩ : Σ k : Fin m, α k) = p := by
          rintro ⟨k, a⟩ rfl
          rfl
        exact hmk (y j) (hall j)
      push Not at hnot_all
      obtain ⟨j₀, hj₀⟩ := hnot_all
      have hw0 : P_law.weight y = 0 := by
        rw [SparseFock.FiniteLaw.independentProduct_weight]
        exact Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [μ, dif_neg hj₀])
      rw [hw0, zero_mul]
    rw [hsub, Finset.sum_image (fun x₁ _ x₂ _ h => hemb_inj h)]
    unfold E_val prodExpectReal prodWeight
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    · rw [SparseFock.FiniteLaw.independentProduct_weight]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp [emb, μ]
    · dsimp only
      rw [spectralNorm_eq_l2_opNorm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [emb, P_mat]
  -- Key bound for every `u > 0` via `θ = (u + ℓ / 3)⁻¹`:
  -- `E_val ≤ u * L + v / (2 * u) + (ℓ / 3) * L`
  have hbound_for_u : ∀ u : ℝ, 0 < u → E_val ≤ u * L + v / (2 * u) + (ℓ / 3) * L := by
    intro u hu
    set D_u : ℝ := u + ℓ / 3
    have hDu_pos : 0 < D_u := by positivity
    set θ : ℝ := D_u⁻¹
    have hθ : 0 < θ := inv_pos.mpr hDu_pos
    have hθDu : θ * D_u = 1 := inv_mul_cancel₀ hDu_pos.ne'
    have hθℓ : θ * ℓ < 3 := by
      have hℓ_lt : ℓ < 3 * D_u := by dsimp [D_u]; linarith
      calc θ * ℓ < θ * (3 * D_u) := mul_lt_mul_of_pos_left hℓ_lt hθ
        _ = 3 * (θ * D_u) := by ring
        _ = 3 := by rw [hθDu, mul_one]
    have h1_sub : 1 - θ * ℓ / 3 = θ * u := by
      have : θ * u + θ * ℓ / 3 = θ * D_u := by dsimp [D_u]; ring
      linarith
    have hc_eq : ((θ ^ 2 / 2) / (1 - θ * ℓ / 3)) = θ / (2 * u) := by
      rw [h1_sub]
      have hθne : θ ≠ 0 := hθ.ne'
      have hune : u ≠ 0 := hu.ne'
      field_simp
    -- Apply `bernstein_iteration` to both `+P_mat` and `-P_mat`
    have hit_pos := bernstein_iteration μ P_mat v_coord hθ hℓ0 hθℓ
      hP_herm hP_mean hP_norm hP_var Finset.univ
    have hit_neg := bernstein_iteration μ (fun j w => -P_mat j w) v_coord hθ hℓ0 hθℓ
      (fun j w => (hP_herm j w).neg)
      (fun j => by simp [smul_neg, Finset.sum_neg_distrib, hP_mean j])
      (fun j w => by rw [norm_neg]; exact hP_norm j w)
      (fun j => by simpa [neg_sq] using hP_var j)
      Finset.univ
    have hc_nonneg : 0 ≤ (θ ^ 2 / 2) / (1 - θ * ℓ / 3) := by
      rw [hc_eq]
      positivity
    have hexp_v : Real.exp (((θ ^ 2 / 2) / (1 - θ * ℓ / 3)) * ∑ j : Fin m, v_coord j) ≤
        Real.exp ((θ / (2 * u)) * v) := by
      rw [← hc_eq]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv_sum hc_nonneg)
    have hpt_norm : ∀ y : Fin m → Σ k : Fin m, α k,
        Real.exp (θ * ‖∑ j : Fin m, P_mat j (y j)‖) ≤
          (NormedSpace.exp (θ • ∑ j : Fin m, P_mat j (y j))).trace +
            (NormedSpace.exp (θ • ∑ j : Fin m, -P_mat j (y j))).trace := by
      intro y
      have hSH : (∑ j : Fin m, P_mat j (y j)).IsHermitian :=
        Matrix.isHermitian_iff_isSymm.mpr <| by
          rw [Matrix.IsSymm, Matrix.transpose_sum]
          exact Finset.sum_congr rfl fun j _ =>
            Matrix.isHermitian_iff_isSymm.mp (hP_herm j (y j))
      have hneg_sum : (-θ) • (∑ j : Fin m, P_mat j (y j)) =
          θ • ∑ j : Fin m, -P_mat j (y j) := by
        rw [Finset.sum_neg_distrib, smul_neg, neg_smul]
      rw [← hneg_sum]
      exact exp_norm_le_two_sided_trace_exp hd _ hSH hθ.le
    have hjensen : Real.exp (θ * E_val) ≤
        P_law.expect (fun y => Real.exp (θ * ‖∑ j : Fin m, P_mat j (y j)‖)) := by
      rw [hE_eq, ← SparseFock.FiniteLaw.expect_smul]
      exact SparseStack.exp_expect_le_expect_exp P_law _
    have htot : Real.exp (θ * E_val) ≤ 2 * (d : ℝ) * Real.exp ((θ / (2 * u)) * v) := by
      calc Real.exp (θ * E_val)
          ≤ P_law.expect (fun y => Real.exp (θ * ‖∑ j : Fin m, P_mat j (y j)‖)) := hjensen
        _ ≤ P_law.expect (fun y =>
              (NormedSpace.exp (θ • ∑ j : Fin m, P_mat j (y j))).trace +
                (NormedSpace.exp (θ • ∑ j : Fin m, -P_mat j (y j))).trace) :=
            P_law.expect_mono hpt_norm
        _ = P_law.expect (fun y =>
              (NormedSpace.exp (θ • ∑ j : Fin m, P_mat j (y j))).trace) +
              P_law.expect (fun y =>
                (NormedSpace.exp (θ • ∑ j : Fin m, -P_mat j (y j))).trace) :=
            P_law.expect_add _ _
        _ ≤ (d : ℝ) * Real.exp (((θ ^ 2 / 2) / (1 - θ * ℓ / 3)) * ∑ j : Fin m, v_coord j) +
              (d : ℝ) * Real.exp (((θ ^ 2 / 2) / (1 - θ * ℓ / 3)) * ∑ j : Fin m, v_coord j) :=
            add_le_add hit_pos hit_neg
        _ ≤ (d : ℝ) * Real.exp ((θ / (2 * u)) * v) +
              (d : ℝ) * Real.exp ((θ / (2 * u)) * v) := by
            gcongr
        _ = 2 * (d : ℝ) * Real.exp ((θ / (2 * u)) * v) := by ring
    have hrhs_exp : 2 * (d : ℝ) * Real.exp ((θ / (2 * u)) * v) =
        Real.exp (L + (θ / (2 * u)) * v) := by
      rw [Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < 2 * (d : ℝ))]
    rw [hrhs_exp] at htot
    have hθE : θ * E_val ≤ L + (θ / (2 * u)) * v := Real.exp_le_exp.mp htot
    have hmul_Du := mul_le_mul_of_nonneg_left hθE hDu_pos.le
    have h1 : D_u * (θ * E_val) = E_val := by
      calc D_u * (θ * E_val) = (θ * D_u) * E_val := by ring
        _ = E_val := by rw [hθDu, one_mul]
    have h2 : D_u * (L + (θ / (2 * u)) * v) = u * L + v / (2 * u) + (ℓ / 3) * L := by
      have hDuθ : D_u * (θ / (2 * u)) = 1 / (2 * u) := by
        calc D_u * (θ / (2 * u)) = (θ * D_u) / (2 * u) := by ring
          _ = 1 / (2 * u) := by rw [hθDu]
      calc D_u * (L + (θ / (2 * u)) * v)
          = D_u * L + (D_u * (θ / (2 * u))) * v := by ring
        _ = (u + ℓ / 3) * L + (1 / (2 * u)) * v := by rw [hDuθ]
        _ = u * L + v / (2 * u) + (ℓ / 3) * L := by ring
    linarith
  -- Optimize over `u > 0`
  rcases hv0.eq_or_lt with rfl | hv_pos
  · simp only [mul_zero, zero_mul, Real.sqrt_zero, zero_add]
    by_contra hgt
    push Not at hgt
    set gap : ℝ := E_val - (ℓ / 3) * L
    have hgap_pos : 0 < gap := sub_pos.mpr hgt
    have hu_pos : 0 < gap / (2 * L) := div_pos hgap_pos (by positivity)
    have hb := hbound_for_u (gap / (2 * L)) hu_pos
    have hsimp : (gap / (2 * L)) * L + 0 / (2 * (gap / (2 * L))) + (ℓ / 3) * L =
        (ℓ / 3) * L + gap / 2 := by
      have hLne : L ≠ 0 := hL_pos.ne'
      field_simp
      ring
    rw [hsimp] at hb
    dsimp [gap] at hb
    linarith
  · set S_v : ℝ := Real.sqrt (2 * v * L)
    have hSv_pos : 0 < S_v := Real.sqrt_pos.mpr (by positivity)
    set u₀ : ℝ := S_v / (2 * L)
    have hu₀_pos : 0 < u₀ := div_pos hSv_pos (by positivity)
    have hb := hbound_for_u u₀ hu₀_pos
    have hSv_sq : S_v ^ 2 = 2 * v * L := Real.sq_sqrt (by positivity)
    have hopt : u₀ * L + v / (2 * u₀) = S_v := by
      have hLne : L ≠ 0 := hL_pos.ne'
      have hSvne : S_v ≠ 0 := hSv_pos.ne'
      dsimp [u₀]
      have hterm2 : v / (2 * (S_v / (2 * L))) = S_v / 2 := by
        rw [div_eq_iff (by positivity : 2 * (S_v / (2 * L)) ≠ 0)]
        calc v = (2 * v * L) / (2 * L) := by field_simp
          _ = S_v ^ 2 / (2 * L) := by rw [hSv_sq]
          _ = S_v / 2 * (2 * (S_v / (2 * L))) := by field_simp
      have hterm1 : S_v / (2 * L) * L = S_v / 2 := by field_simp
      rw [hterm1, hterm2]
      ring
    linarith

/-! ## Section D: Lemma 5.3 and Both Forms of Lemma 2.4 -/

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

/-- **Lemma 5.3 (Expected squared operator norm in the independent-entry model, p. 31).** -/
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
    rw [spectralNorm_eq_l2_opNorm, iidTernaryMatrix_eq_iidMatrix (by omega)]
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

/-- **Lemma 2.4 (Isolated cross-term operator norm, ambient off-`I` form, pp. 12, 29, 33).** -/
theorem lemma_2_4_IsolatedCrossTerm : Lemma_2_4_IsolatedCrossTerm := by
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

/-- **Lemma 2.4 (Disjoint `(I, J)` submatrix `W ∈ ℝ^{|J|×d}` form, pp. 12, 29, 33).** -/
theorem lemma_2_4_IsolatedCrossTerm_Submatrix : Lemma_2_4_IsolatedCrossTerm_Submatrix := by
  obtain ⟨C_cg, hC_pos, h0d, h0I, hmain⟩ := lemma_2_4_IsolatedCrossTerm
  refine ⟨C_cg, hC_pos, ?_, ?_, ?_⟩
  · intro ζ b n I J ω W
    rw [OsiUb.Prelim.spectralNorm_isolatedSubmatrixCross_eq, h0d, spectralNorm_eq_l2_opNorm,
      norm_zero]
  · intro ζ b n d J ω W
    rw [OsiUb.Prelim.spectralNorm_isolatedSubmatrixCross_eq, h0I, spectralNorm_eq_l2_opNorm,
      norm_zero]
  · intro ζ b n d p hζ hbζ hd hp hplog I J W hIJ hI hW ω₀
    have hfn : (fun ω : SketchSample ζ b n =>
        spectralNorm (isolatedSubmatrixCross I J W (mergeHeadSample I ω₀ ω))) =
        (fun ω => spectralNorm (retainedCrossGram I (embedSubmatrix J W)
          (mergeHeadSample I ω₀ ω))) := by
      funext ω
      exact OsiUb.Prelim.spectralNorm_isolatedSubmatrixCross_eq I J W (mergeHeadSample I ω₀ ω)
    rw [hfn]
    exact hmain ζ b n d p hζ hbζ hd hp hplog I (embedSubmatrix J W) hI
      (OsiUb.Prelim.embedSubmatrix_isIsometry J W hW)
      (OsiUb.Prelim.embedSubmatrix_zero_of_disjoint hIJ W) ω₀

/-! ## Section E: Claim 5.4 (Single-Block Coupling) & Lemma 5.5 (Coupling Jensen) -/

private def fin3EquivEta : Fin 3 ≃ SparseFock.EtaOutcome where
  toFun t := if t.val = 0 then .neg else if t.val = 1 then .zero else .pos
  invFun
    | .neg => 0
    | .zero => 1
    | .pos => 2
  left_inv t := by fin_cases t <;> rfl
  right_inv z := by cases z <;> rfl

private def boolEquivSign : Bool ≃ SparseFock.SparseStackModel.Sign where
  toFun
    | true => .plus
    | false => .minus
  invFun
    | .plus => true
    | .minus => false
  left_inv β := by cases β <;> rfl
  right_inv s := by cases s <;> rfl

/-- **Claim 5.4 (Single-block CountSketch / i.i.d. ternary coupling, p. 32, Eq. (31)).** -/
theorem claim_5_4_SingleBlockCoupling : Claim_5_4_SingleBlockCoupling := by
  have hcstar_lt : (1 - Real.exp (-1))⁻¹ < 2 := by
    have he : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num)]
      linarith [Real.exp_one_gt_d9]
    have hpos : 0 < 1 - Real.exp (-1) := by linarith
    rw [inv_eq_one_div, div_lt_iff₀ hpos]
    linarith
  refine ⟨hcstar_lt, fun b hb => ?_⟩
  have hb0 : 0 < b := hb
  have hcB_eq : couplingCB b = SparseFock.SparseIIDCoupling.cB b := rfl
  rw [hcB_eq]
  refine ⟨SparseFock.SparseIIDCoupling.one_le_cB hb0,
    SparseFock.SparseIIDCoupling.cB_le_cStar hb0, ?_⟩
  let eY : (Fin b → Fin 3) ≃ SparseFock.SparseIIDCoupling.YVector b :=
    Equiv.piCongrRight (fun _ => fin3EquivEta)
  let eX : (Fin b × Bool) ≃ SparseFock.SparseStackDistribution.SignedHash b :=
    Equiv.prodCongr (Equiv.refl (Fin b)) boolEquivSign
  let eYX := Equiv.prodCongr eY eX
  let J : ((Fin b → Fin 3) × (Fin b × Bool)) → ℝ :=
    fun p => (SparseFock.SparseIIDCoupling.jointColumnLaw hb0).weight (eYX p)
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun p => (SparseFock.SparseIIDCoupling.jointColumnLaw hb0).weight_nonneg (eYX p), ?_⟩
    simpa [J] using eYX.sum_comp (SparseFock.SparseIIDCoupling.jointColumnLaw hb0).weight
      |>.trans (SparseFock.SparseIIDCoupling.jointColumnLaw hb0).sum_weight
  · intro η
    have hsum : (∑ ξ : Fin b × Bool, J (η, ξ)) =
        ∑ x : SparseFock.SparseStackDistribution.SignedHash b,
          (SparseFock.SparseIIDCoupling.jointColumnLaw hb0).weight (eY η, x) :=
      eX.sum_comp (fun x => (SparseFock.SparseIIDCoupling.jointColumnLaw hb0).weight (eY η, x))
    rw [hsum]
    simp_rw [SparseFock.SparseIIDCoupling.jointColumnLaw_weight]
    rw [← Finset.mul_sum, SparseFock.SparseIIDCoupling.sum_kernelWeight hb0, mul_one,
      SparseFock.SparseIIDCoupling.yVectorLaw_weight]
    refine Finset.prod_congr rfl fun u _ => ?_
    have hm : ∀ t : Fin 3,
        SparseFock.TernaryJacobi.mass b (fin3EquivEta t) = ternaryCoordMass b t := by
      intro t
      fin_cases t <;> rfl
    exact hm (η u)
  · intro ξ
    have hsum : (∑ η : Fin b → Fin 3, J (η, ξ)) =
        SparseFock.SparseIIDCoupling.xMarginal hb0 (eX ξ) :=
      eY.sum_comp (fun y => (SparseFock.SparseIIDCoupling.jointColumnLaw hb0).weight (y, eX ξ))
    rw [hsum, SparseFock.SparseIIDCoupling.xMarginal_eq_selectorWeight hb0 (eX ξ)]
    rfl
  · intro ξ u'
    have hden : (∑ η : Fin b → Fin 3, J (η, ξ)) =
        (SparseFock.SparseStackDistribution.selectorLaw b hb0).weight (eX ξ) := by
      have hsum : (∑ η : Fin b → Fin 3, J (η, ξ)) =
          SparseFock.SparseIIDCoupling.xMarginal hb0 (eX ξ) :=
        eY.sum_comp (fun y => (SparseFock.SparseIIDCoupling.jointColumnLaw hb0).weight (y, eX ξ))
      rw [hsum, SparseFock.SparseIIDCoupling.xMarginal_eq_selectorWeight hb0 (eX ξ)]
    have hyval : ∀ t : Fin 3,
        SparseFock.SparseIIDCoupling.yValue (fin3EquivEta t) = ternaryVal t := by
      intro t
      fin_cases t <;> rfl
    have hnum : (∑ η : Fin b → Fin 3, J (η, ξ) * ternaryVal (η u')) =
        ∑ y : SparseFock.SparseIIDCoupling.YVector b,
          (SparseFock.SparseIIDCoupling.jointColumnLaw hb0).weight (y, eX ξ) *
            SparseFock.SparseIIDCoupling.yValue (y u') := by
      rw [← eY.sum_comp (fun y =>
        (SparseFock.SparseIIDCoupling.jointColumnLaw hb0).weight (y, eX ξ) *
          SparseFock.SparseIIDCoupling.yValue (y u'))]
      refine Finset.sum_congr rfl fun η _ => ?_
      simp [J, eYX, eY, hyval]
    rw [hnum, hden, Finset.sum_div]
    simp_rw [← div_mul_eq_mul_div]
    have hcond : (∑ y : SparseFock.SparseIIDCoupling.YVector b,
        (SparseFock.SparseIIDCoupling.jointColumnLaw hb0).weight (y, eX ξ) /
          (SparseFock.SparseStackDistribution.selectorLaw b hb0).weight (eX ξ) *
            SparseFock.SparseIIDCoupling.yValue (y u')) =
        (SparseFock.SparseIIDCoupling.conditionalYLaw hb0 (eX ξ)).expect
          (fun y => SparseFock.SparseIIDCoupling.yValue (y u')) := rfl
    rw [hcond, SparseFock.SparseIIDCoupling.conditional_expect_yValue hb0 (eX ξ) u']
    have hcB_inv : (SparseFock.SparseIIDCoupling.cB b)⁻¹ =
        1 - SparseFock.SparseIIDCoupling.p0 b := by
      rw [SparseFock.SparseIIDCoupling.cB, inv_inv]
    have hsgn : (eX ξ).2.val = signValue ξ.2 := by
      change (boolEquivSign ξ.2).val = signValue ξ.2
      cases ξ.2 <;> rfl
    have hx1 : (eX ξ).1 = ξ.1 := rfl
    rw [hcB_inv, hx1, hsgn]
    by_cases hu' : u' = ξ.1 <;> simp [hu', mul_comm]

private lemma uniformMeanReal_equiv {S₁ S₂ : Type} [Fintype S₁] [Fintype S₂]
    (e : S₁ ≃ S₂) (f₁ : S₁ → ℝ) (f₂ : S₂ → ℝ) (h : ∀ x : S₁, f₁ x = f₂ (e x)) :
    uniformMeanReal S₁ f₁ = uniformMeanReal S₂ f₂ := by
  unfold uniformMeanReal
  rw [Fintype.card_congr e, Fintype.sum_equiv e f₁ f₂ h]

private noncomputable def aggU {ζ n : ℕ} (I J : Finset (Fin n))
    (y : I × J → Fin ζ → SparseFock.EtaOutcome) : Matrix I J ℝ :=
  fun i j => (ζ : ℝ)⁻¹ * ∑ t : Fin ζ, SparseFock.SparseIIDCoupling.yValue (y (i, j) t)

private lemma fullMat_embedSubmatrix_mulVec_eq {ζ n d : ℕ} (I J : Finset (Fin n))
    (W : Matrix J (Fin d) ℝ) (x : Fin n × Fin n → Fin ζ → SparseFock.EtaOutcome)
    (f : Fin d → ℝ) (i : I) :
    (((ζ : ℝ)⁻¹ • (SparseStack.Cross.fullMat I x * embedSubmatrix J W)).mulVec f) i.1 =
      ((aggU I J (fun p : I × J => x (p.1.1, p.2.1)) * W).mulVec f) i := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    SparseStack.Cross.fullMat, Matrix.of_apply, i.2, ↓reduceIte,
    SparseStack.Cross.rowSum, aggU]
  rw [Finset.mul_sum]
  have hsub_J : (∑ j : Fin n, (ζ : ℝ)⁻¹ *
      ((∑ t : Fin ζ, SparseFock.SparseIIDCoupling.yValue (x (i.1, j) t)) *
        embedSubmatrix J W j l)) =
      ∑ j ∈ J, (ζ : ℝ)⁻¹ *
        ((∑ t : Fin ζ, SparseFock.SparseIIDCoupling.yValue (x (i.1, j) t)) *
          embedSubmatrix J W j l) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ J) fun j _ hj => ?_
    simp [embedSubmatrix, hj]
  rw [hsub_J, ← Finset.sum_attach J, Finset.univ_eq_attach]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hemb : embedSubmatrix J W j.1 l = W j l := dif_pos j.2
  rw [hemb, mul_assoc]

/-- **Lemma 5.5 (Conditional Jensen coupling bound for the isolated cross-term, p. 32, Eq. (32)).** -/
theorem lemma_5_5_CouplingJensen : Lemma_5_5_CouplingJensen := by
  intro ζ b n d _hζ hb I J W hIJ ω₀
  have hb0 : 0 < b := hb
  set V : Matrix (Fin n) (Fin d) ℝ := embedSubmatrix J W
  have hVsupp : ∀ i ∈ I, ∀ l : Fin d, V i l = 0 :=
    OsiUb.Prelim.embedSubmatrix_zero_of_disjoint hIJ W
  -- Step 1: Rewrite LHS as `(sketchLaw ζ b n hb0).expect` of `‖crossGram I V ...‖`
  have hlhs : uniformMeanReal (SketchSample ζ b n)
      (fun ω => spectralNorm (isolatedSubmatrixCross I J W (mergeHeadSample I ω₀ ω))) =
      (SparseStack.sketchLaw ζ b n hb0).expect
        (fun ω => ‖SparseStack.crossGram I V (SparseStack.mergeHead I ω₀ ω)‖) := by
    rw [uniformMeanReal_sketchSample_eq_expect hb0]
    refine SparseFock.FiniteLaw.expect_congr _ fun ω => ?_
    rw [OsiUb.Prelim.spectralNorm_isolatedSubmatrixCross_eq, spectralNorm_eq_l2_opNorm,
      retainedCrossGram_eq_crossGram]
    rfl
  -- Step 2: Apply `expect_sketchLaw_toRaw`, `crossGram_mergeHead_eq`, `coupling_bound`, and `restore_bound`
  have hstep : (SparseStack.sketchLaw ζ b n hb0).expect
      (fun ω => ‖SparseStack.crossGram I V (SparseStack.mergeHead I ω₀ ω)‖) ≤
      couplingCB b * (SparseStack.Cross.aggLaw ζ n b hb0).expect
        (fun x => ‖(ζ : ℝ)⁻¹ • (SparseStack.Cross.fullMat I x * V)‖) := by
    have hstruct : (SparseStack.sketchLaw ζ b n hb0).expect
        (fun ω => ‖SparseStack.crossGram I V (SparseStack.mergeHead I ω₀ ω)‖) =
        (SparseFock.SparseStackDistribution.rawSampleLaw ζ b n hb0).expect
          (fun z => ‖SparseStack.Cross.structMat I ω₀ V
            (fun p => SparseStack.Cross.selVec (z p))‖) := by
      rw [← SparseStack.Cross.expect_sketchLaw_toRaw hb0]
      exact SparseFock.FiniteLaw.expect_congr _ fun ω => by
        rw [SparseStack.Cross.crossGram_mergeHead_eq I V hVsupp ω₀ ω]
    rw [hstruct]
    exact (SparseStack.Cross.coupling_bound hb0 I ω₀ V).trans
      (mul_le_mul_of_nonneg_left (SparseStack.Cross.restore_bound hb0 I ω₀ V)
        (SparseStack.Cross.cB_pos hb0).le)
  -- Step 3: Show `‖(ζ : ℝ)⁻¹ • (fullMat I x * V)‖` depends only on `I × J` and matches `aggSubmatrix`
  have hnorm_sub : ∀ x : Fin n × Fin n → Fin ζ → SparseFock.EtaOutcome,
      ‖(ζ : ℝ)⁻¹ • (SparseStack.Cross.fullMat I x * V)‖ =
        ‖aggU I J (fun p : I × J => x (p.1.1, p.2.1)) * W‖ := by
    intro x
    rw [← spectralNorm_eq_l2_opNorm, ← spectralNorm_eq_l2_opNorm]
    apply OsiUb.Prelim.spectralNorm_eq_of_forall_mulVec_sq
    intro f
    set M_amb : Matrix (Fin n) (Fin d) ℝ := (ζ : ℝ)⁻¹ • (SparseStack.Cross.fullMat I x * V)
    set M_sub : Matrix I (Fin d) ℝ := aggU I J (fun p : I × J => x (p.1.1, p.2.1)) * W
    have hzero_out : ∀ i : Fin n, i ∉ I → M_amb.mulVec f i = 0 := by
      intro i hi
      simp [M_amb, SparseStack.Cross.fullMat, Matrix.mulVec, dotProduct, Matrix.mul_apply, hi]
    have hsub_I : (∑ i : Fin n, (M_amb.mulVec f i) ^ 2) =
        ∑ i ∈ I, (M_amb.mulVec f i) ^ 2 := by
      symm
      refine Finset.sum_subset (Finset.subset_univ I) fun i _ hi => ?_
      simp [hzero_out i hi]
    rw [hsub_I, ← Finset.sum_attach I, Finset.univ_eq_attach]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show M_amb.mulVec f i.1 = M_sub.mulVec f i from
        fullMat_embedSubmatrix_mulVec_eq I J W x f i]
  -- Step 4: Marginalize `aggLaw ζ n b hb0` to `I × J` via `expect_select` and match `IidBlockTernarySample`
  have hmarg : (SparseStack.Cross.aggLaw ζ n b hb0).expect
      (fun x => ‖aggU I J (fun p : I × J => x (p.1.1, p.2.1)) * W‖) =
      (SparseFock.FiniteLaw.independentProduct
        (fun _ : I × J => SparseStack.Cross.rowLaw ζ b hb0)).expect
        (fun y => ‖aggU I J y * W‖) := by
    have hsel := SparseStack.Cross.expect_select (SparseStack.Cross.rowLaw ζ b hb0)
      (fun _ : I × J => True) (fun p : I × J => (p.1.1, p.2.1))
      (fun p p' _ _ h => by
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact Prod.ext (Subtype.ext h1) (Subtype.ext h2))
      (fun _ a => a) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun y => ‖aggU I J y * W‖)
    simpa [SparseStack.Cross.aggLaw, SparseFock.FiniteLaw.expect_const] using hsel
  have hrhs : (SparseFock.FiniteLaw.independentProduct
      (fun _ : I × J => SparseStack.Cross.rowLaw ζ b hb0)).expect
      (fun y => ‖aggU I J y * W‖) =
      uniformMeanReal (IidBlockTernarySample ζ I J b)
        (fun x => spectralNorm (aggSubmatrix ζ I J b x * W)) := by
    rw [SparseStack.Cross.rowLaw,
      SparseStack.Cross.expect_nested_eq_flat (SparseFock.SparseIIDCoupling.coordinateLaw b hb0),
      ← uniformMeanReal_mapOutcome_eq_expect hb hb0]
    let e_idx : IidBlockTernarySample ζ I J b ≃ ((I × J) × Fin ζ → Fin (2 * b)) :=
      { toFun := fun x p => x p.2 p.1.1 p.1.2
        invFun := fun z t i j => z ((i, j), t)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    symm
    refine uniformMeanReal_equiv e_idx _ _ fun x => ?_
    have hmat : aggU I J (fun a c => mapOutcome (e_idx x (a, c))) = aggSubmatrix ζ I J b x := by
      ext i j
      simp [aggU, aggSubmatrix, e_idx, iidTernaryEntry_eq_yValue]
    dsimp only
    rw [spectralNorm_eq_l2_opNorm, hmat]
  rw [hlhs, ← hrhs, ← hmarg, ← SparseFock.FiniteLaw.expect_congr _ hnorm_sub]
  exact hstep

/-! ## Section F: Claim 5.6 (Symmetric Convex Dominance) & Lemma 5.7 (Full Sketch Moment) -/

/-- **Claim 5.6 (Symmetric bounded convex dominance, p. 34, Eq. (42)).** -/
theorem claim_5_6_SymmetricConvexDom : Claim_5_6_SymmetricConvexDom := by
  intro B hB Ω _ p hp V hsymm hbd habs φ hφ
  have hB0 : 0 < B := by omega
  let μ : SparseFock.FiniteLaw Ω := ⟨p, hp.1, hp.2⟩
  have h2q : μ.expect (fun ω => |V ω|) ≤ 2 * (1 / (B : ℝ)) := by
    have h0 : (0 : ℝ) ≤ 1 / (B : ℝ) := by positivity
    have h1 : μ.expect (fun ω => |V ω|) ≤ 1 / (B : ℝ) := habs
    linarith
  have hcx := SparseStack.Cross.convex_order_symm μ V hsymm hbd h2q φ hφ
  have hunif : uniformMeanReal (Fin (2 * B)) (fun u => φ (2 * iidTernaryEntry u)) =
      (1 - 1 / (B : ℝ)) * φ 0 + (1 / (2 * (B : ℝ))) * (φ 2 + φ (-2)) := by
    let e1 : (Unit → Fin (2 * B)) ≃ Fin (2 * B) := Equiv.funUnique Unit (Fin (2 * B))
    have hstep1 : uniformMeanReal (Fin (2 * B)) (fun u => φ (2 * iidTernaryEntry u)) =
        uniformMeanReal (Unit → Fin (2 * B))
          (fun x => φ (2 * (SparseFock.TernaryJacobi.eta B (mapOutcome (x ())) /
            Real.sqrt (B : ℝ)))) := by
      unfold uniformMeanReal
      rw [Fintype.card_congr e1.symm, ← e1.sum_comp]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [e1, iidTernaryEntry_eq_eta_div_sqrt (by omega : 1 ≤ B)]
    have hstep15 := uniformMeanReal_mapOutcome_eq_expect (κ := Unit) (B := B) (by omega) hB0
      (fun z => φ (2 * (SparseFock.TernaryJacobi.eta B (z ()) / Real.sqrt (B : ℝ))))
    rw [hstep1, hstep15]
    have hstep2 : (SparseFock.FiniteLaw.independentProduct
        (fun _ : Unit => SparseFock.SparseIIDCoupling.coordinateLaw B hB0)).expect
        (fun z => φ (2 * (SparseFock.TernaryJacobi.eta B (z ()) / Real.sqrt (B : ℝ)))) =
        (SparseFock.TernaryJacobi.law B hB0).expect
          (fun z => φ (2 * (SparseFock.TernaryJacobi.eta B z / Real.sqrt (B : ℝ)))) :=
      SparseFock.FiniteLaw.expect_independentProduct_apply
        (fun _ : Unit => SparseFock.SparseIIDCoupling.coordinateLaw B hB0) ()
        (fun z => φ (2 * (SparseFock.TernaryJacobi.eta B z / Real.sqrt (B : ℝ))))
    rw [hstep2, SparseStack.Cross.expect_ternary_two hB0 φ]
    ring
  refine ⟨?_, hunif⟩
  rw [hunif]
  have hcx' : pmfExpectReal p (fun ω => φ (V ω)) ≤
      (1 - 1 / (B : ℝ)) * φ 0 + 1 / (B : ℝ) / 2 * (φ 2 + φ (-2)) := hcx
  have hdiv : (1 : ℝ) / (B : ℝ) / 2 = 1 / (2 * (B : ℝ)) := by ring
  rw [hdiv] at hcx'
  exact hcx'

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

/-- **Lemma 5.7 (High-moment bound for the full SparseStack Gram error, p. 35, Eq. (47)).** -/
theorem lemma_5_7_FullSketchMoment : Lemma_5_7_FullSketchMoment := by
  refine ⟨by positivity, ?_⟩
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
  refine href.trans ?_
  set S_env : ℝ := Real.sqrt (((D : ℝ) + 2 * (p : ℝ) + 1) / ((b : ℝ) * (ζ : ℝ))) +
    ((D : ℝ) + 2 * (p : ℝ) + 1) / ((b : ℝ) * (ζ : ℝ)) +
    (2 * (p : ℝ) + 1) / (ζ : ℝ)
  have hS0 : 0 ≤ S_env := by dsimp [S_env]; positivity
  have h34 : (34 : ℝ) ≤ 12 * (3 + Real.sqrt 2) := by linarith [Real.sqrt_nonneg 2]
  gcongr

end OsiUb.UpperBound
