import Osi.Spec
import SparseStack.SmallBall
import SparseStack.Rounding
import SparseStack.Localization
import SparseStack.Linearization
import SparseStack.Prob.Tails

/-!
# Sections 2–4: Flat-Vector Preservation, Lattice Rounding, and Common Support

Proves `Lemma_3_2_WeightedBernoulli`, `Lemma_3_3_PointwiseFlat`, `Lemma_3_4_LatticeRounding`,
`Theorem_2_1_FlatPreservation`, `Lemma_4_1_GaussianTruncation`, `Lemma_4_2_MinimaxSelection`, and
`Theorem_2_2_CommonSupport` in full unspecialized generality (`ε ∈ (0, 1)`, `δ_loc ∈ (0, 1)`,
general measure-theoretic `P`, arbitrary `H ⪰ 0`).
-/

namespace Osi.UpperBound

open Osi.Spec
open scoped BigOperators

/-! ## Section A: Bridges between `Osi.Spec` and `SparseStack` -/

private lemma vecSqNorm_eq_sqNorm {ι : Type} [Fintype ι] (v : ι → ℝ) :
    vecSqNorm v = SparseStack.sqNorm v :=
  (SparseStack.Loc.sqNorm_eq_sum_sq v).symm

private lemma distSparseSq_eq {n : ℕ} (m : ℕ) (z : Fin n → ℝ) :
    distSparseSq m z = SparseStack.distSparseSq m z :=
  rfl

private lemma uniformProb_eq {S : Type} [Fintype S] (E : S → Prop) :
    uniformProb S E = SparseStack.uniformProb S E :=
  rfl

private lemma sparseStackOmega_transpose_mulVec_apply {ζ b n : ℕ} (ω : SketchSample ζ b n)
    (w : Fin n → ℝ) (j : Fin (ζ * b)) :
    (sparseStackOmega ω).transpose.mulVec w j =
      (SparseStack.sketchMatrix ω).mulVec w (finProdFinEquiv.symm j) :=
  rfl

private lemma vecSqNorm_sparseStackOmega_transpose_mulVec {ζ b n : ℕ} (ω : SketchSample ζ b n)
    (w : Fin n → ℝ) :
    vecSqNorm ((sparseStackOmega ω).transpose.mulVec w) =
      SparseStack.sqNorm ((SparseStack.sketchMatrix ω).mulVec w) := by
  rw [vecSqNorm, SparseStack.Loc.sqNorm_eq_sum_sq]
  exact Fintype.sum_equiv finProdFinEquiv.symm
    (fun j => ((sparseStackOmega ω).transpose.mulVec w j) ^ 2)
    (fun p => ((SparseStack.sketchMatrix ω).mulVec w p) ^ 2)
    (fun j => by rw [sparseStackOmega_transpose_mulVec_apply])

private lemma vecSqNorm_sparseStackOmega_mul_mulVec {ζ b n r : ℕ} (ω : SketchSample ζ b n)
    (Q : Matrix (Fin n) (Fin r) ℝ) (x : Fin r → ℝ) :
    vecSqNorm (((sparseStackOmega ω).transpose * Q).mulVec x) =
      SparseStack.sqNorm ((SparseStack.sketchMatrix ω * Q).mulVec x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact vecSqNorm_sparseStackOmega_transpose_mulVec ω (Q.mulVec x)

/-! ## Section B: Lemma 3.2 (Weighted Bernoulli lower tail) -/

/-- Elementary lower bound `u / 2 ≤ 1 - exp(-u)` for `u ∈ [0, 1]`, via `exp(-u) ≤ (1 + u)⁻¹`. -/
private lemma half_le_one_sub_exp_neg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have h1u : 0 < u + 1 := by linarith
  have hexp : Real.exp (-u) ≤ (u + 1)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ h1u (Real.add_one_le_exp u)
  have hrat : (u + 1)⁻¹ ≤ 1 - u / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ h1u]
    nlinarith
  linarith

/-- Single-factor MGF bound for a `{0, 1}`-valued measurable variable `B` with `P(B = 1) ≥ p₀`. -/
private lemma bernoulli_mgf_factor_le {Ω_prob : Type} [MeasurableSpace Ω_prob]
    (P : MeasureTheory.Measure Ω_prob) [MeasureTheory.IsProbabilityMeasure P]
    {B : Ω_prob → ℝ} (hB_meas : Measurable B) (h01 : ∀ ω, B ω = 0 ∨ B ω = 1)
    {p₀ : ℝ} (hp₀ : 0 < p₀) (hpB : p₀ ≤ (P {ω : Ω_prob | B ω = 1}).toReal)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∫ ω, Real.exp (-u * B ω) ∂P) ≤ Real.exp (-(p₀ / 2) * u) := by
  set S : Set Ω_prob := {ω : Ω_prob | B ω = 1}
  have hS_meas : MeasurableSet S := hB_meas (measurableSet_singleton (1 : ℝ))
  have hB_ind : B = S.indicator (1 : Ω_prob → ℝ) := by
    funext ω
    by_cases h1 : B ω = 1
    · have hmem : ω ∈ S := h1
      simp [Set.indicator_of_mem hmem, h1]
    · have hnot : ω ∉ S := h1
      rcases h01 ω with h0 | h1'
      · simp [Set.indicator_of_notMem hnot, h0]
      · exact absurd h1' h1
  have hB_int : MeasureTheory.Integrable B P := by
    rw [hB_ind]
    exact (MeasureTheory.integrable_const (1 : ℝ)).indicator hS_meas
  have hEB : (∫ ω, B ω ∂P) = (P S).toReal := by
    rw [hB_ind, MeasureTheory.integral_indicator_one hS_meas, MeasureTheory.measureReal_def]
  have hpt : ∀ ω, Real.exp (-u * B ω) = 1 - (1 - Real.exp (-u)) * B ω := by
    intro ω
    rcases h01 ω with h0 | h1
    · simp [h0]
    · simp [h1]
  have hint_eq : (∫ ω, Real.exp (-u * B ω) ∂P) = 1 - (1 - Real.exp (-u)) * (P S).toReal := by
    simp_rw [hpt]
    rw [MeasureTheory.integral_sub (MeasureTheory.integrable_const (1 : ℝ))
      (hB_int.const_mul (1 - Real.exp (-u))),
      MeasureTheory.integral_const, MeasureTheory.integral_const_mul, hEB]
    simp
  have hu_bound : u / 2 ≤ 1 - Real.exp (-u) := half_le_one_sub_exp_neg hu0 hu1
  have h1_nonneg : 0 ≤ 1 - Real.exp (-u) := by linarith
  have hprod_ge : (p₀ / 2) * u ≤ (1 - Real.exp (-u)) * (P S).toReal := calc
    (p₀ / 2) * u = (u / 2) * p₀ := by ring
    _ ≤ (1 - Real.exp (-u)) * p₀ := mul_le_mul_of_nonneg_right hu_bound hp₀.le
    _ ≤ (1 - Real.exp (-u)) * (P S).toReal := mul_le_mul_of_nonneg_left hpB h1_nonneg
  have hexp_le : 1 - (p₀ / 2) * u ≤ Real.exp (-(p₀ / 2) * u) := by
    linarith [Real.add_one_le_exp (-(p₀ / 2) * u)]
  linarith

/-- **Lemma 3.2 (Weighted Bernoulli lower tail, p. 16).** -/
theorem lemma_3_2_WeightedBernoulli : Lemma_3_2_WeightedBernoulli := by
  intro p₀ hp₀
  refine ⟨p₀ / 4, p₀ / 4, by positivity, by positivity, ?_⟩
  intro m Ω_prob _ P hP B v v_max hindep hB_meas h01 hpB hv hv_max _hVpos
  set u : Fin m → ℝ := fun j => v j / v_max
  have hu0 : ∀ j, 0 ≤ u j := fun j => div_nonneg (hv j).1 hv_max.le
  have hu1 : ∀ j, u j ≤ 1 := fun j => (div_le_one hv_max).mpr (hv j).2
  set F : Ω_prob → ℝ := fun ω => Real.exp (-(∑ j : Fin m, v j * B j ω) / v_max)
  have hF_prod : ∀ ω, F ω = ∏ j : Fin m, Real.exp (-u j * B j ω) := by
    intro ω
    simp only [F, u]
    rw [← Real.exp_sum]
    congr 1
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hf_meas : ∀ j : Fin m, Measurable (fun x : ℝ => Real.exp (-u j * x)) :=
    fun j => Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)
  have hF_meas : Measurable F := by
    have hsum : Measurable (fun ω => ∑ j : Fin m, v j * B j ω) :=
      Finset.measurable_sum Finset.univ (fun j _ => measurable_const.mul (hB_meas j))
    exact Real.continuous_exp.measurable.comp (hsum.neg.div_const v_max)
  have hF_pos : ∀ ω, 0 ≤ F ω := fun ω => (Real.exp_pos _).le
  have hF_le_one : ∀ ω, ‖F ω‖ ≤ 1 := by
    intro ω
    rw [Real.norm_of_nonneg (hF_pos ω)]
    have hsum_nonneg : 0 ≤ ∑ j : Fin m, v j * B j ω := by
      refine Finset.sum_nonneg (fun j _ => mul_nonneg (hv j).1 ?_)
      rcases h01 j ω with h0 | h1 <;> linarith
    have harg_nonpos : -(∑ j : Fin m, v j * B j ω) / v_max ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsum_nonneg) hv_max.le
    exact Real.exp_le_one_iff.mpr harg_nonpos
  have hF_int : MeasureTheory.Integrable F P :=
    (MeasureTheory.integrable_const (1 : ℝ)).mono' hF_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall hF_le_one)
  have hMGF_fact : (∫ ω, F ω ∂P) = ∏ j : Fin m, ∫ ω, Real.exp (-u j * B j ω) ∂P := by
    simp_rw [hF_prod]
    exact hindep.integral_fun_prod_comp (fun j => (hB_meas j).aemeasurable)
      (fun j => (hf_meas j).aestronglyMeasurable)
  have hMGF_le : (∫ ω, F ω ∂P) ≤ Real.exp (-(p₀ / 2) * (∑ j : Fin m, v j) / v_max) := by
    rw [hMGF_fact]
    calc (∏ j : Fin m, ∫ ω, Real.exp (-u j * B j ω) ∂P)
        ≤ ∏ j : Fin m, Real.exp (-(p₀ / 2) * u j) := by
          refine Finset.prod_le_prod ?_ ?_
          · intro j _
            exact MeasureTheory.integral_nonneg (fun ω => (Real.exp_pos _).le)
          · intro j _
            exact bernoulli_mgf_factor_le P (hB_meas j) (h01 j) hp₀ (hpB j) (hu0 j) (hu1 j)
      _ = Real.exp (-(p₀ / 2) * (∑ j : Fin m, v j) / v_max) := by
          rw [← Real.exp_sum]
          congr 1
          simp only [u]
          rw [← Finset.mul_sum, ← Finset.sum_div, mul_div_assoc']
  set thr : ℝ := Real.exp (-(p₀ / 4) * (∑ j : Fin m, v j) / v_max)
  have hthr_pos : 0 < thr := Real.exp_pos _
  have hsub : {ω : Ω_prob | (∑ j : Fin m, v j * B j ω) < (p₀ / 4) * (∑ j : Fin m, v j)} ⊆
      {ω : Ω_prob | thr ≤ F ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, thr, F] at hω ⊢
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff_of_pos_right hv_max]
    linarith
  have hmono : (P {ω : Ω_prob | (∑ j : Fin m, v j * B j ω) < (p₀ / 4) * (∑ j : Fin m, v j)}).toReal ≤
      P.real {ω : Ω_prob | thr ≤ F ω} := by
    rw [MeasureTheory.measureReal_def]
    exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top P _) (MeasureTheory.measure_mono hsub)
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hF_pos) hF_int thr
  have hdiv : P.real {ω : Ω_prob | thr ≤ F ω} ≤ (∫ ω, F ω ∂P) / thr := by
    rw [le_div_iff₀ hthr_pos, mul_comm]
    exact hmarkov
  calc (P {ω : Ω_prob | (∑ j : Fin m, v j * B j ω) < (p₀ / 4) * (∑ j : Fin m, v j)}).toReal
      ≤ (∫ ω, F ω ∂P) / thr := hmono.trans hdiv
    _ ≤ Real.exp (-(p₀ / 2) * (∑ j : Fin m, v j) / v_max) / thr :=
        div_le_div_of_nonneg_right hMGF_le hthr_pos.le
    _ = Real.exp (-(p₀ / 4) * (∑ j : Fin m, v j) / v_max) := by
        simp only [thr, ← Real.exp_sub]
        congr 1
        ring

/-! ## Section C: Lemma 3.3 (Pointwise flat bound) & Lemma 3.4 (Lattice rounding net) -/

/-- **Lemma 3.3 (Pointwise lower bound for flat tail vectors, p. 17).** -/
theorem lemma_3_3_PointwiseFlat : Lemma_3_3_PointwiseFlat := by
  refine ⟨Real.sqrt (2 / 81), 1 / 3200, Real.sqrt_pos.mpr (by norm_num), by norm_num, ?_⟩
  intro ζ b n h z a D hζ hb ha hdisj hz hD1 hDb hzinf
  have hζ0 : 0 < ζ := hζ
  have hb0 : 0 < b := hb
  have hz' : SparseStack.sqNorm z = 1 := by rwa [← vecSqNorm_eq_sqNorm]
  have hzinf' : ∀ i : Fin n, z i ^ 2 ≤ 1 / D := by
    intro i
    rw [one_div]
    exact hzinf i
  have hc0 : (Real.sqrt (2 / 81) * a) ^ 2 = 2 / 81 * a ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hprob : uniformProb (SketchSample ζ b n)
      (fun ω => vecSqNorm ((sparseStackOmega ω).transpose.mulVec (h + a • z)) <
        (Real.sqrt (2 / 81) * a) ^ 2) =
      (SparseStack.sketchLaw ζ b n hb0).prob
        {ω | SparseStack.sqNorm ((SparseStack.sketchMatrix ω).mulVec (h + a • z)) <
          2 / 81 * a ^ 2} := by
    rw [uniformProb_eq, SparseStack.uniformProb_eq_prob hb0]
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, vecSqNorm_sparseStackOmega_transpose_mulVec, hc0]
  rw [hprob, show -(1 / 3200 : ℝ) * (ζ : ℝ) * D = -((ζ : ℝ) * D) / 3200 by ring]
  exact SparseStack.small_ball hζ0 hb0 h z a ha hdisj hz' D hD1 hDb hzinf'

/-- **Lemma 3.4 (Unbiased lattice rounding net, p. 18).** -/
theorem lemma_3_4_LatticeRounding : Lemma_3_4_LatticeRounding := by
  intro r η hr hη0 hη1
  obtain ⟨N, hcard, hnorm, hround⟩ := SparseStack.lattice_net r hr η hη0 hη1
  refine ⟨N, hcard, ?_, ?_⟩
  · intro y hy
    rw [vecSqNorm_eq_sqNorm]
    exact hnorm y hy
  · intro k T x hx
    rw [vecSqNorm_eq_sqNorm] at hx
    obtain ⟨y, hyN, hxy, hTxy⟩ := hround (Fin k) T x hx
    refine ⟨y, hyN, ?_, ?_⟩
    · rw [vecSqNorm_eq_sqNorm]
      exact hxy
    · rw [vecSqNorm_eq_sqNorm]
      exact hTxy

/-! ## Section D: Theorem 2.1 (Uniform preservation of flat vectors) -/

/-- Deterministic net-center transfer for general `(ε, F_fac)` with `lam = ε / 10` and
`η = ε / (20 √F_fac + 10)`. -/
private lemma loc_center_good_gen {n r : ℕ} {k : Type} [Fintype k] (m : ℕ)
    (Q : Matrix (Fin n) (Fin r) ℝ) (hQ : Q.transpose * Q = 1)
    (X : Matrix k (Fin r) ℝ) (x y : Fin r → ℝ)
    {ε F_fac : ℝ} (hε0 : 0 < ε) (hF_pos : 0 < F_fac)
    (hx2 : ε ^ 2 ≤ distSparseSq m (Q.mulVec x))
    (hx3 : SparseStack.sqNorm (X.mulVec x) < ((1 / 10 : ℝ) * ε) ^ 2)
    (hr : 1 ≤ r) (hF : SparseStack.frobSq X < F_fac * (r : ℝ))
    (hxy : SparseStack.sqNorm (x - y) ≤ (ε / (20 * Real.sqrt F_fac + 10)) ^ 2)
    (hTxy : SparseStack.sqNorm (X.mulVec (x - y)) ≤
      (ε / (20 * Real.sqrt F_fac + 10)) ^ 2 / (4 * (r : ℝ)) * SparseStack.frobSq X) :
    (ε - ε / (20 * Real.sqrt F_fac + 10)) ^ 2 ≤ distSparseSq m (Q.mulVec y) ∧
      SparseStack.sqNorm (X.mulVec y) <
        2 / 81 * (ε - ε / (20 * Real.sqrt F_fac + 10)) ^ 2 := by
  set η : ℝ := ε / (20 * Real.sqrt F_fac + 10)
  have hden : 0 < 20 * Real.sqrt F_fac + 10 := by positivity
  have hη0 : 0 < η := div_pos hε0 hden
  have hη_eq : η * (20 * Real.sqrt F_fac + 10) = ε := div_mul_cancel₀ ε hden.ne'
  have hη_le : η ≤ ε / 10 := by
    have : 0 ≤ η * (20 * Real.sqrt F_fac) := by positivity
    linarith
  have h910 : (9 / 10 : ℝ) * ε ≤ ε - η := by linarith
  have hεη_pos : 0 < ε - η := by linarith
  simp only [distSparseSq_eq] at hx2 ⊢
  constructor
  · have h1 := SparseStack.sqrt_distSparseSq_le m (Q.mulVec x) (Q.mulVec y)
    rw [← Matrix.mulVec_sub, SparseStack.Loc.sqNorm_mulVec_of_isometry Q hQ] at h1
    have h2 : Real.sqrt (SparseStack.sqNorm (x - y)) ≤ η :=
      (Real.sqrt_le_left hη0.le).mpr hxy
    have h3 : ε ≤ Real.sqrt (SparseStack.distSparseSq m (Q.mulVec x)) :=
      (Real.le_sqrt hε0.le (SparseStack.distSparseSq_nonneg _ _)).mpr hx2
    have h4 : ε - η ≤ Real.sqrt (SparseStack.distSparseSq m (Q.mulVec y)) := by linarith
    have h5 := pow_le_pow_left₀ hεη_pos.le h4 2
    rwa [Real.sq_sqrt (SparseStack.distSparseSq_nonneg _ _)] at h5
  · have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have h1 : Real.sqrt (SparseStack.sqNorm (X.mulVec y)) ≤
        Real.sqrt (SparseStack.sqNorm (X.mulVec x)) +
          Real.sqrt (SparseStack.sqNorm (X.mulVec (x - y))) := by
      have h := SparseStack.Loc.sqrt_sqNorm_sub_le (X.mulVec x) (X.mulVec (x - y))
      rwa [show X.mulVec x - X.mulVec (x - y) = X.mulVec y by
        rw [Matrix.mulVec_sub, sub_sub_cancel]] at h
    have hηF_le : η * Real.sqrt F_fac / 2 ≤ ε / 40 := by
      have : 0 ≤ 10 * η := by positivity
      linarith
    have hsq_eq : η ^ 2 / (4 * (r : ℝ)) * (F_fac * (r : ℝ)) = (η * Real.sqrt F_fac / 2) ^ 2 := by
      calc η ^ 2 / (4 * (r : ℝ)) * (F_fac * (r : ℝ))
          = η ^ 2 * F_fac / 4 := by field_simp
        _ = η ^ 2 * (Real.sqrt F_fac ^ 2) / 4 := by rw [Real.sq_sqrt hF_pos.le]
        _ = (η * Real.sqrt F_fac / 2) ^ 2 := by ring
    have h2 : SparseStack.sqNorm (X.mulVec (x - y)) ≤ (ε / 40) ^ 2 := by
      calc SparseStack.sqNorm (X.mulVec (x - y))
          ≤ η ^ 2 / (4 * (r : ℝ)) * SparseStack.frobSq X := hTxy
        _ ≤ η ^ 2 / (4 * (r : ℝ)) * (F_fac * (r : ℝ)) :=
            mul_le_mul_of_nonneg_left hF.le (by positivity)
        _ = (η * Real.sqrt F_fac / 2) ^ 2 := hsq_eq
        _ ≤ (ε / 40) ^ 2 := pow_le_pow_left₀ (by positivity) hηF_le 2
    have h3 : Real.sqrt (SparseStack.sqNorm (X.mulVec (x - y))) ≤ ε / 40 :=
      (Real.sqrt_le_left (by positivity)).mpr h2
    have h4 : Real.sqrt (SparseStack.sqNorm (X.mulVec x)) < (1 / 10 : ℝ) * ε := by
      calc Real.sqrt (SparseStack.sqNorm (X.mulVec x))
          < Real.sqrt (((1 / 10 : ℝ) * ε) ^ 2) :=
            Real.sqrt_lt_sqrt (SparseStack.Loc.sqNorm_nonneg _) hx3
        _ = (1 / 10 : ℝ) * ε := Real.sqrt_sq (by positivity)
    have h5 : Real.sqrt (SparseStack.sqNorm (X.mulVec y)) < (1 / 8 : ℝ) * ε := by linarith
    have h6 : SparseStack.sqNorm (X.mulVec y) < ((1 / 8 : ℝ) * ε) ^ 2 :=
      (Real.sqrt_lt' (by positivity)).mp h5
    have h7 : ((9 / 10 : ℝ) * ε) ^ 2 ≤ (ε - η) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h910 2
    nlinarith [sq_pos_of_pos hε0]

/-- Single net-center tail bound for arbitrary `(η, ε, Θ, M_loc)`. -/
private lemma loc_prob_center_le_gen {n r ζ b m : ℕ} (hζ : 0 < ζ) (hb : 0 < b) (hζr : ζ ≤ r)
    {ε η Θ M_loc : ℝ} (hη0 : 0 < η) (hεη : 0 < ε - η) (hΘ1 : 1 ≤ Θ)
    (hMc : Θ ≤ M_loc * ((ε - η) ^ 2 / (1 + η) ^ 2))
    (hζm : M_loc * (r : ℝ) ≤ (ζ : ℝ) * (m : ℝ))
    (hζb : Θ * (r : ℝ) ≤ (ζ : ℝ) * (b : ℝ))
    (Q : Matrix (Fin n) (Fin r) ℝ) (hQ : Q.transpose * Q = 1)
    (y : Fin r → ℝ) (hy : SparseStack.sqNorm y ≤ (1 + η) ^ 2) :
    (SparseStack.sketchLaw ζ b n hb).prob
        {ω | (ε - η) ^ 2 ≤ distSparseSq m (Q.mulVec y) ∧
          SparseStack.sqNorm ((SparseStack.sketchMatrix ω * Q).mulVec y) <
            2 / 81 * (ε - η) ^ 2} ≤
      2 * Real.exp (-(Θ * (r : ℝ)) / 3200) := by
  simp only [distSparseSq_eq]
  set d : ℝ := SparseStack.distSparseSq m (Q.mulVec y)
  by_cases hd : (ε - η) ^ 2 ≤ d
  · have hdpos : 0 < d := lt_of_lt_of_le (sq_pos_of_pos hεη) hd
    obtain ⟨h, z, hw, hdisj, hz, hzi⟩ := SparseStack.topm_decomposition m (Q.mulVec y) hdpos
    have ha : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
    have ha2 : Real.sqrt d ^ 2 = d := Real.sq_sqrt hdpos.le
    have hζ0 : (0 : ℝ) < ζ := by exact_mod_cast hζ
    have hζr' : (ζ : ℝ) ≤ r := by exact_mod_cast hζr
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hζ0 hζr'
    set c : ℝ := (ε - η) ^ 2 / (1 + η) ^ 2
    have hc0 : 0 < c := by positivity
    have hmM : M_loc ≤ (m : ℝ) := by
      have h1 : M_loc * (r : ℝ) ≤ (r : ℝ) * (m : ℝ) :=
        hζm.trans (mul_le_mul_of_nonneg_right hζr' (Nat.cast_nonneg m))
      exact le_of_mul_le_mul_right (by linarith) hr0
    have hmc1 : 1 ≤ (m : ℝ) * c := by
      calc (1 : ℝ) ≤ Θ := hΘ1
        _ ≤ M_loc * c := hMc
        _ ≤ (m : ℝ) * c := mul_le_mul_of_nonneg_right hmM hc0.le
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    set D : ℝ := min (b : ℝ) ((m : ℝ) * c)
    have hD1 : 1 ≤ D := le_min hb1 hmc1
    have hDb : D ≤ b := min_le_left _ _
    have hDmc : D ≤ (m : ℝ) * c := min_le_right _ _
    have hzinf : ∀ i : Fin n, z i ^ 2 ≤ 1 / D := by
      intro i
      have hD0 : 0 < D := by linarith
      rw [le_div_iff₀ hD0]
      have h1 : (m : ℝ) * d * z i ^ 2 ≤ SparseStack.sqNorm y := by
        simpa only [SparseStack.Loc.sqNorm_mulVec_of_isometry Q hQ] using hzi i
      have h1η2 : 0 < (1 + η) ^ 2 := by positivity
      calc z i ^ 2 * D ≤ z i ^ 2 * ((m : ℝ) * c) :=
            mul_le_mul_of_nonneg_left hDmc (sq_nonneg _)
        _ = (m : ℝ) * (ε - η) ^ 2 * z i ^ 2 / (1 + η) ^ 2 := by
            simp only [c]
            ring
        _ ≤ (m : ℝ) * d * z i ^ 2 / (1 + η) ^ 2 := by gcongr
        _ ≤ SparseStack.sqNorm y / (1 + η) ^ 2 := by gcongr
        _ ≤ 1 := (div_le_one h1η2).mpr hy
    have hζD : Θ * (r : ℝ) ≤ (ζ : ℝ) * D := by
      have hmc : Θ * (r : ℝ) ≤ (ζ : ℝ) * ((m : ℝ) * c) := by
        calc Θ * (r : ℝ) ≤ (M_loc * c) * (r : ℝ) := mul_le_mul_of_nonneg_right hMc hr0.le
          _ = (M_loc * (r : ℝ)) * c := by ring
          _ ≤ ((ζ : ℝ) * (m : ℝ)) * c := mul_le_mul_of_nonneg_right hζm hc0.le
          _ = (ζ : ℝ) * ((m : ℝ) * c) := by ring
      rcases le_total (b : ℝ) ((m : ℝ) * c) with hle | hle
      · simp only [D, min_eq_left hle]
        exact hζb
      · simp only [D, min_eq_right hle]
        exact hmc
    have hSB := SparseStack.small_ball hζ hb h z (Real.sqrt d) ha hdisj hz D hD1 hDb hzinf
    calc (SparseStack.sketchLaw ζ b n hb).prob
          {ω | (ε - η) ^ 2 ≤ d ∧
            SparseStack.sqNorm ((SparseStack.sketchMatrix ω * Q).mulVec y) <
              2 / 81 * (ε - η) ^ 2}
        ≤ (SparseStack.sketchLaw ζ b n hb).prob
          {ω | SparseStack.sqNorm ((SparseStack.sketchMatrix ω).mulVec (h + Real.sqrt d • z)) <
            2 / 81 * Real.sqrt d ^ 2} := by
          apply SparseFock.FiniteLaw.prob_mono
          intro ω hω
          obtain ⟨_, hω2⟩ := hω
          show SparseStack.sqNorm ((SparseStack.sketchMatrix ω).mulVec (h + Real.sqrt d • z)) <
            2 / 81 * Real.sqrt d ^ 2
          rw [← hw, Matrix.mulVec_mulVec, ha2]
          linarith
      _ ≤ 2 * Real.exp (-((ζ : ℝ) * D) / 3200) := hSB
      _ ≤ 2 * Real.exp (-(Θ * (r : ℝ)) / 3200) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          linarith
  · have hempty : {ω : SketchSample ζ b n | (ε - η) ^ 2 ≤ d ∧
        SparseStack.sqNorm ((SparseStack.sketchMatrix ω * Q).mulVec y) <
          2 / 81 * (ε - η) ^ 2} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h
      exact absurd h hd
    rw [hempty, SparseFock.FiniteLaw.prob_empty]
    positivity

/-- Net-size times small-ball exponential bound when `3200 * (log(16 / η) + 1) ≤ Θ`. -/
private lemma loc_net_exp_le_gen {η Θ : ℝ} (hη0 : 0 < η)
    (hΘ : 3200 * (Real.log (16 / η) + 1) ≤ Θ) (r : ℕ) :
    (16 / η) ^ r * Real.exp (-(Θ * (r : ℝ)) / 3200) ≤ Real.exp (-(r : ℝ)) := by
  have h16 : 0 < 16 / η := by positivity
  have hbase : (16 / η) * Real.exp (-Θ / 3200) ≤ Real.exp (-1) := by
    rw [← Real.exp_log h16, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  calc (16 / η) ^ r * Real.exp (-(Θ * (r : ℝ)) / 3200)
      = ((16 / η) * Real.exp (-Θ / 3200)) ^ r := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
    _ ≤ Real.exp (-1) ^ r := pow_le_pow_left₀ (by positivity) hbase r
    _ = Real.exp (-(r : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- **Theorem 2.1 (Uniform preservation of flat vectors, pp. 7, 19).** -/
theorem theorem_2_1_FlatPreservation : Theorem_2_1_FlatPreservation := by
  refine ⟨1 / 10, by norm_num, ?_⟩
  intro ε δ_loc hε0 hε1 hδ0 _hδ1
  set F_fac : ℝ := 2 / δ_loc
  have hF_pos : 0 < F_fac := div_pos (by norm_num) hδ0
  set η : ℝ := ε / (20 * Real.sqrt F_fac + 10)
  have hden : 0 < 20 * Real.sqrt F_fac + 10 := by positivity
  have hη0 : 0 < η := div_pos hε0 hden
  have hη_eq : η * (20 * Real.sqrt F_fac + 10) = ε := div_mul_cancel₀ ε hden.ne'
  have hη_le : η ≤ ε / 10 := by
    have : 0 ≤ η * (20 * Real.sqrt F_fac) := by positivity
    linarith
  have hη1 : η < 1 := by linarith
  have hεη : 0 < ε - η := by linarith
  set c : ℝ := (ε - η) ^ 2 / (1 + η) ^ 2
  have hc0 : 0 < c := by positivity
  set lam : ℝ := (1 / 10 : ℝ) * ε
  set Θ : ℝ := max 1 (3200 * (Real.log (16 / η) + 1))
  set M_loc : ℝ := max 1 (Θ / c)
  set r₀ : ℕ := max 1 (Nat.ceil (Real.log (4 / δ_loc)))
  have hΘ1 : 1 ≤ Θ := le_max_left 1 _
  have hΘ_log : 3200 * (Real.log (16 / η) + 1) ≤ Θ := le_max_right 1 _
  have hM1 : 1 ≤ M_loc := le_max_left 1 _
  have hMc : Θ ≤ M_loc * c := by
    have h : Θ / c ≤ M_loc := le_max_right 1 _
    rwa [div_le_iff₀ hc0] at h
  have hr₀1 : 1 ≤ r₀ := le_max_left 1 _
  refine ⟨lam, Θ, M_loc, r₀, le_rfl, hΘ1, hM1, hr₀1, ?_⟩
  intro n r ζ b m hr₀ _hrn hζ hζr hb hζb hζm Q hQ
  have hr1 : 1 ≤ r := hr₀1.trans hr₀
  have hζ0 : 0 < ζ := hζ
  have hb0 : 0 < b := hb
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hζb' : Θ * (r : ℝ) ≤ (ζ : ℝ) * (b : ℝ) := by exact_mod_cast hζb
  obtain ⟨N, hNcard, hNnorm, hNround⟩ := SparseStack.lattice_net r hr1 η hη0 hη1
  set CE : (Fin r → ℝ) → Set (SketchSample ζ b n) := fun y =>
    {ω | (ε - η) ^ 2 ≤ distSparseSq m (Q.mulVec y) ∧
      SparseStack.sqNorm ((SparseStack.sketchMatrix ω * Q).mulVec y) < 2 / 81 * (ε - η) ^ 2}
  have hprob_eq : uniformProb (SketchSample ζ b n)
      (fun ω => ∃ x : Fin r → ℝ,
        vecSqNorm x = 1 ∧ ε ^ 2 ≤ distSparseSq m (Q.mulVec x) ∧
          vecSqNorm (((sparseStackOmega ω).transpose * Q).mulVec x) < lam ^ 2) =
      (SparseStack.sketchLaw ζ b n hb0).prob
        {ω | ∃ x : Fin r → ℝ,
          SparseStack.sqNorm x = 1 ∧ ε ^ 2 ≤ distSparseSq m (Q.mulVec x) ∧
            SparseStack.sqNorm ((SparseStack.sketchMatrix ω * Q).mulVec x) < lam ^ 2} := by
    rw [uniformProb_eq, SparseStack.uniformProb_eq_prob hb0]
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, vecSqNorm_sparseStackOmega_mul_mulVec]
    simp only [vecSqNorm_eq_sqNorm]
  rw [hprob_eq]
  have hsub : {ω : SketchSample ζ b n | ∃ x : Fin r → ℝ,
      SparseStack.sqNorm x = 1 ∧ ε ^ 2 ≤ distSparseSq m (Q.mulVec x) ∧
        SparseStack.sqNorm ((SparseStack.sketchMatrix ω * Q).mulVec x) < lam ^ 2} ⊆
      {ω | F_fac * (r : ℝ) ≤ SparseStack.frobSq (SparseStack.sketchMatrix ω * Q)} ∪
        ⋃ y ∈ N, CE y := by
    intro ω hω
    obtain ⟨x, hx1, hx2, hx3⟩ := hω
    by_cases hF : F_fac * (r : ℝ) ≤ SparseStack.frobSq (SparseStack.sketchMatrix ω * Q)
    · exact Or.inl hF
    · right
      push Not at hF
      obtain ⟨y, hyN, hxy, hTxy⟩ := hNround (Fin ζ × Fin b) (SparseStack.sketchMatrix ω * Q) x hx1
      rw [Set.mem_iUnion₂]
      exact ⟨y, hyN, loc_center_good_gen m Q hQ (SparseStack.sketchMatrix ω * Q) x y
        hε0 hF_pos hx2 hx3 hr1 hF hxy hTxy⟩
  have hF₁ : (SparseStack.sketchLaw ζ b n hb0).prob
      {ω | F_fac * (r : ℝ) ≤ SparseStack.frobSq (SparseStack.sketchMatrix ω * Q)} ≤ δ_loc / 2 := by
    have hmk := SparseFock.FiniteLaw.markov (SparseStack.sketchLaw ζ b n hb0)
      (f := fun ω => SparseStack.frobSq (SparseStack.sketchMatrix ω * Q))
      (fun _ => SparseStack.Loc.frobSq_nonneg _)
      (threshold := F_fac * (r : ℝ)) (by positivity)
    rw [SparseStack.expect_frobSq (s := ζ) hζ0 hb0 Q hQ] at hmk
    calc (SparseStack.sketchLaw ζ b n hb0).prob
          {ω | F_fac * (r : ℝ) ≤ SparseStack.frobSq (SparseStack.sketchMatrix ω * Q)}
        ≤ (r : ℝ) / (F_fac * (r : ℝ)) := hmk
      _ = δ_loc / 2 := by
          simp only [F_fac]
          field_simp
  have hE : ∀ y ∈ N, (SparseStack.sketchLaw ζ b n hb0).prob (CE y) ≤
      2 * Real.exp (-(Θ * (r : ℝ)) / 3200) :=
    fun y hy => loc_prob_center_le_gen hζ0 hb0 hζr hη0 hεη hΘ1 hMc hζm hζb' Q hQ y (hNnorm y hy)
  have hnet := loc_net_exp_le_gen hη0 hΘ_log r
  have hr_tail : 2 * Real.exp (-(r : ℝ)) ≤ δ_loc / 2 := by
    have hlog_le : Real.log (4 / δ_loc) ≤ (r : ℝ) := by
      have hceil : Nat.ceil (Real.log (4 / δ_loc)) ≤ r₀ := le_max_right 1 _
      have hr0_le : Nat.ceil (Real.log (4 / δ_loc)) ≤ r := hceil.trans hr₀
      exact (Nat.le_ceil _).trans (by exact_mod_cast hr0_le)
    have h4_pos : 0 < 4 / δ_loc := by positivity
    have hexp_r : 4 / δ_loc ≤ Real.exp (r : ℝ) := by
      rw [← Real.exp_log h4_pos]
      exact Real.exp_le_exp.mpr hlog_le
    have hpos_expr : 0 < Real.exp (r : ℝ) := Real.exp_pos _
    rw [Real.exp_neg, show (2 : ℝ) * (Real.exp (r : ℝ))⁻¹ = 2 / Real.exp (r : ℝ) by ring,
      div_le_div_iff₀ hpos_expr (by norm_num)]
    have hmul := (div_le_iff₀ hδ0).mp hexp_r
    linarith
  refine le_trans ((SparseStack.sketchLaw ζ b n hb0).prob_mono hsub) ?_
  calc (SparseStack.sketchLaw ζ b n hb0).prob
        ({ω | F_fac * (r : ℝ) ≤ SparseStack.frobSq (SparseStack.sketchMatrix ω * Q)} ∪
          ⋃ y ∈ N, CE y)
      ≤ (SparseStack.sketchLaw ζ b n hb0).prob
          {ω | F_fac * (r : ℝ) ≤ SparseStack.frobSq (SparseStack.sketchMatrix ω * Q)} +
          (SparseStack.sketchLaw ζ b n hb0).prob (⋃ y ∈ N, CE y) :=
        SparseStack.prob_union_le _ _ _
    _ ≤ δ_loc / 2 + ∑ y ∈ N, (SparseStack.sketchLaw ζ b n hb0).prob (CE y) :=
        add_le_add hF₁ (SparseStack.prob_union_le_sum _ N _)
    _ ≤ δ_loc / 2 + ∑ _y ∈ N, 2 * Real.exp (-(Θ * (r : ℝ)) / 3200) := by
        gcongr with y hy
        exact hE y hy
    _ = δ_loc / 2 + (N.card : ℝ) * (2 * Real.exp (-(Θ * (r : ℝ)) / 3200)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ δ_loc / 2 + (16 / η) ^ r * (2 * Real.exp (-(Θ * (r : ℝ)) / 3200)) := by
        gcongr
    _ = δ_loc / 2 + 2 * ((16 / η) ^ r * Real.exp (-(Θ * (r : ℝ)) / 3200)) := by ring
    _ ≤ δ_loc / 2 + 2 * Real.exp (-(r : ℝ)) := by gcongr
    _ ≤ δ_loc / 2 + δ_loc / 2 := by linarith
    _ = δ_loc := by ring

/-! ## Section E: Lemma 4.1 (Gaussian / fourth-moment truncation lower bound) -/

private lemma measurable_distSparseSq {Ω_prob : Type} [MeasurableSpace Ω_prob] {n : ℕ} (m : ℕ)
    {g : Ω_prob → Fin n → ℝ} (hg : ∀ i : Fin n, Measurable (fun ω => g ω i)) :
    Measurable (fun ω => distSparseSq m (g ω)) := by
  unfold distSparseSq
  exact Measurable.iInf (fun I =>
    Finset.measurable_sum (I.1)ᶜ (fun i _ => (hg i).pow_const 2))

private lemma integrable_distSparseSq {Ω_prob : Type} [MeasurableSpace Ω_prob]
    {P : MeasureTheory.Measure Ω_prob} {n : ℕ} (m : ℕ) {g : Ω_prob → Fin n → ℝ}
    (hg_meas : ∀ i : Fin n, Measurable (fun ω => g ω i))
    (hg2 : ∀ i : Fin n, MeasureTheory.Integrable (fun ω => (g ω i) ^ 2) P) :
    MeasureTheory.Integrable (fun ω => distSparseSq m (g ω)) P := by
  have hsum_int : MeasureTheory.Integrable (fun ω => ∑ i : Fin n, (g ω i) ^ 2) P :=
    MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hg2 i)
  refine hsum_int.mono' (measurable_distSparseSq m hg_meas).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [distSparseSq_eq, Real.norm_of_nonneg (SparseStack.Lin.distSparseSq_nonneg_aux m (g ω))]
  calc SparseStack.distSparseSq m (g ω) ≤ SparseStack.sqNorm (g ω) :=
        SparseStack.Lin.distSparseSq_le_sqNorm_aux m (g ω)
    _ = ∑ i : Fin n, (g ω i) ^ 2 := SparseStack.Loc.sqNorm_eq_sum_sq (g ω)

private lemma integrable_min_sq {Ω_prob : Type} [MeasurableSpace Ω_prob]
    {P : MeasureTheory.Measure Ω_prob} {G : Ω_prob → ℝ}
    (hG_meas : Measurable G) (hG2 : MeasureTheory.Integrable (fun ω => G ω ^ 2) P)
    {T : ℝ} (hT : 0 ≤ T) :
    MeasureTheory.Integrable (fun ω => min (G ω ^ 2) T) P := by
  have hmeas : Measurable (fun ω => min (G ω ^ 2) T) :=
    Measurable.min (hG_meas.pow_const 2) measurable_const
  refine hG2.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_of_nonneg (le_min (sq_nonneg _) hT)]
  exact min_le_left _ _

/-- Measure-theoretic one-coordinate moment bound: if `E[G⁴] ≤ 3 (E[G²])²` and `t ≥ 0`, then
`(3/4) min(E[G²], t) ≤ E[min(G², 3 t)]`. -/
private lemma coord_trunc_integral_bound {Ω_prob : Type} [MeasurableSpace Ω_prob]
    (P : MeasureTheory.Measure Ω_prob) {G : Ω_prob → ℝ}
    (hG_meas : Measurable G)
    (hG2 : MeasureTheory.Integrable (fun ω => G ω ^ 2) P)
    (hG4 : MeasureTheory.Integrable (fun ω => G ω ^ 4) P)
    (h4 : (∫ ω, G ω ^ 4 ∂P) ≤ 3 * (∫ ω, G ω ^ 2 ∂P) ^ 2)
    {t : ℝ} (ht : 0 ≤ t) :
    (3 / 4 : ℝ) * min (∫ ω, G ω ^ 2 ∂P) t ≤ ∫ ω, min (G ω ^ 2) (3 * t) ∂P := by
  set A : ℝ := ∫ ω, G ω ^ 2 ∂P
  have hA0 : 0 ≤ A := MeasureTheory.integral_nonneg (fun ω => sq_nonneg (G ω))
  rcases ht.eq_or_lt with rfl | htpos
  · have hz : (fun ω => min (G ω ^ 2) (3 * (0 : ℝ))) = fun _ => (0 : ℝ) := by
      funext ω
      rw [mul_zero]
      exact min_eq_right (sq_nonneg _)
    rw [hz, MeasureTheory.integral_zero, min_eq_right hA0, mul_zero]
  · have hmin_int : MeasureTheory.Integrable (fun ω => min (G ω ^ 2) (3 * t)) P :=
      integrable_min_sq hG_meas hG2 (by positivity)
    have hgen : ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
        c * A - c ^ 2 * A ^ 2 / (4 * t) ≤ ∫ ω, min (G ω ^ 2) (3 * t) ∂P := by
      intro c _hc0 hc1
      have hpt : ∀ ω, c * G ω ^ 2 - c ^ 2 / (12 * t) * G ω ^ 4 ≤ min (G ω ^ 2) (3 * t) := by
        intro ω
        have h1 := SparseStack.Lin.sub_sq_div_le_min (c * G ω ^ 2) htpos
        have h2 : min (c * G ω ^ 2) (3 * t) ≤ min (G ω ^ 2) (3 * t) :=
          min_le_min (mul_le_of_le_one_left (sq_nonneg _) hc1) le_rfl
        have h3 : c * G ω ^ 2 - (c * G ω ^ 2) ^ 2 / (12 * t) =
            c * G ω ^ 2 - c ^ 2 / (12 * t) * G ω ^ 4 := by ring
        linarith
      have hsub_int : MeasureTheory.Integrable
          (fun ω => c * G ω ^ 2 - c ^ 2 / (12 * t) * G ω ^ 4) P :=
        (hG2.const_mul c).sub (hG4.const_mul (c ^ 2 / (12 * t)))
      have hE := MeasureTheory.integral_mono hsub_int hmin_int hpt
      rw [MeasureTheory.integral_sub (hG2.const_mul c) (hG4.const_mul (c ^ 2 / (12 * t))),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hE
      have hc2 : 0 ≤ c ^ 2 / (12 * t) := by positivity
      have h5 : c ^ 2 / (12 * t) * (∫ ω, G ω ^ 4 ∂P) ≤ c ^ 2 / (12 * t) * (3 * A ^ 2) :=
        mul_le_mul_of_nonneg_left h4 hc2
      have h6 : c ^ 2 / (12 * t) * (3 * A ^ 2) = c ^ 2 * A ^ 2 / (4 * t) := by
        field_simp
        ring
      linarith
    rcases le_or_gt A t with hAt | hAt
    · have h1 := hgen 1 zero_le_one le_rfl
      simp only [one_pow, one_mul] at h1
      rw [min_eq_left hAt]
      have hAA : A ^ 2 / (4 * t) ≤ A / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    · have hApos : 0 < A := lt_of_le_of_lt ht hAt
      have h1 := hgen (t / A) (by positivity) ((div_le_one hApos).mpr hAt.le)
      rw [min_eq_right hAt.le]
      have h7 : t / A * A - (t / A) ^ 2 * A ^ 2 / (4 * t) = (3 / 4 : ℝ) * t := by
        field_simp
        ring
      linarith

/-- Sorted-sequence identity at index `k₀ = ⟨4 * m, h4m⟩` for an antitone permutation `a ∘ σ`. -/
private lemma antitone_sum_min_sub {n m : ℕ} (h4m : 4 * m < n) (a : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (hanti : Antitone (fun i : Fin n => a (σ i))) :
    (∑ i : Fin n, min (a i) (a (σ ⟨4 * m, h4m⟩))) - (4 * m : ℝ) * a (σ ⟨4 * m, h4m⟩) =
      ∑ i : Fin n, if 4 * m ≤ i.val then a (σ i) else 0 := by
  set k₀ : Fin n := ⟨4 * m, h4m⟩
  set t : ℝ := a (σ k₀)
  rw [← Equiv.sum_comp σ (fun j => min (a j) t),
    ← Finset.sum_add_sum_compl (Finset.Iio k₀) (fun i => min (a (σ i)) t)]
  have h_head : (∑ i ∈ Finset.Iio k₀, min (a (σ i)) t) = (4 * m : ℝ) * t := by
    have hcongr : ∀ i ∈ Finset.Iio k₀, min (a (σ i)) t = t := by
      intro i hi
      exact min_eq_right (hanti (Finset.mem_Iio.mp hi).le)
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Fin.card_Iio, nsmul_eq_mul]
    simp [k₀]
  have h_tail : (∑ i ∈ (Finset.Iio k₀)ᶜ, min (a (σ i)) t) =
      ∑ i : Fin n, if 4 * m ≤ i.val then a (σ i) else 0 := by
    have hcongr : ∀ i ∈ (Finset.Iio k₀)ᶜ, min (a (σ i)) t = a (σ i) := by
      intro i hi
      have hle : k₀ ≤ i := not_lt.mp (Finset.mem_compl.mp hi ∘ Finset.mem_Iio.mpr)
      exact min_eq_left (hanti hle)
    rw [Finset.sum_congr rfl hcongr, ← Finset.sum_filter]
    congr 1
    ext i
    simp [k₀, Fin.lt_def]
  rw [h_head, h_tail]
  ring

/-- **Lemma 4.1 (Truncation lower bound for Gaussian / fourth-moment vectors, p. 21).** -/
theorem lemma_4_1_GaussianTruncation : Lemma_4_1_GaussianTruncation := by
  intro n m h4m Ω_prob _ P hP g hg_meas hg2 hg4 h4 σ hanti
  have hdist_int : MeasureTheory.Integrable (fun ω => distSparseSq m (g ω)) P :=
    integrable_distSparseSq m hg_meas hg2
  refine ⟨hdist_int, ?_⟩
  set a : Fin n → ℝ := fun i => ∫ ω, (g ω i) ^ 2 ∂P
  set k₀ : Fin n := ⟨4 * m, h4m⟩
  set t : ℝ := a (σ k₀)
  have ht0 : 0 ≤ t := MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)
  have hcoord : ∀ i : Fin n,
      (3 / 4 : ℝ) * min (a i) t ≤ ∫ ω, min ((g ω i) ^ 2) (3 * t) ∂P :=
    fun i => coord_trunc_integral_bound P (hg_meas i) (hg2 i) (hg4 i) (h4 i) ht0
  have hmin_int : ∀ i : Fin n, MeasureTheory.Integrable (fun ω => min ((g ω i) ^ 2) (3 * t)) P :=
    fun i => integrable_min_sq (hg_meas i) (hg2 i) (by positivity)
  have hsum_min_int : MeasureTheory.Integrable
      (fun ω => ∑ i : Fin n, min ((g ω i) ^ 2) (3 * t)) P :=
    MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hmin_int i)
  have hlhs_int : MeasureTheory.Integrable
      (fun ω => (∑ i : Fin n, min ((g ω i) ^ 2) (3 * t)) - (m : ℝ) * (3 * t)) P :=
    hsum_min_int.sub (MeasureTheory.integrable_const _)
  have hpt : ∀ ω, (∑ i : Fin n, min ((g ω i) ^ 2) (3 * t)) - (m : ℝ) * (3 * t) ≤
      distSparseSq m (g ω) :=
    fun ω => SparseStack.Lin.sum_min_sub_le_distSparseSq m (g ω) (by positivity)
  have hE := MeasureTheory.integral_mono hlhs_int hdist_int hpt
  rw [MeasureTheory.integral_sub hsum_min_int (MeasureTheory.integrable_const _),
    MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hmin_int i),
    MeasureTheory.integral_const, MeasureTheory.measureReal_def, hP.measure_univ,
    ENNReal.toReal_one, one_smul] at hE
  have hsum_coord : (3 / 4 : ℝ) * (∑ i : Fin n, min (a i) t) ≤
      ∑ i : Fin n, ∫ ω, min ((g ω i) ^ 2) (3 * t) ∂P := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hcoord i)
  have htail := antitone_sum_min_sub h4m a σ hanti
  have h_id : (3 / 4 : ℝ) *
      ((∑ i : Fin n, min (a i) t) - (4 * (m : ℝ)) * t) =
      (3 / 4 : ℝ) * (∑ i : Fin n, min (a i) t) - (m : ℝ) * (3 * t) := by ring
  rw [← htail, h_id]
  linarith

/-! ## Section F: Lemma 4.2 (Minimax selection) & Theorem 2.2 (Common support) -/

private lemma dotProduct_coordRows_gram {n r : ℕ} (S : Finset (Fin n))
    (V : Matrix (Fin n) (Fin r) ℝ) (x : Fin r → ℝ) :
    dotProduct x (((coordRows S V).transpose * coordRows S V).mulVec x) =
      ∑ i ∈ S, (V.mulVec x i) ^ 2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct]
  have hrow : ∀ i : Fin n,
      (coordRows S V).mulVec x i * (coordRows S V).mulVec x i =
        if i ∈ S then (V.mulVec x i) ^ 2 else 0 := by
    intro i
    by_cases hi : i ∈ S
    · simp [coordRows, Matrix.mulVec, dotProduct, hi, sq]
    · simp [coordRows, Matrix.mulVec, dotProduct, hi]
  simp_rw [hrow]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

private lemma loewnerLe_of_rayleigh {n r : ℕ} (S : Finset (Fin n))
    (V : Matrix (Fin n) (Fin r) ℝ) (H : Matrix (Fin r) (Fin r) ℝ) (hH : H.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c)
    (hray : ∀ x : Fin r → ℝ, ∑ i ∈ S, (V.mulVec x i) ^ 2 ≤ c * dotProduct x (H.mulVec x)) :
    LoewnerLe ((coordRows S V).transpose * coordRows S V) (c • H) := by
  unfold LoewnerLe
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · have h1 : (c • H).IsHermitian := (hH.smul hc).isHermitian
    have h2 : ((coordRows S V).transpose * coordRows S V).IsHermitian := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.isHermitian_conjTranspose_mul_self (coordRows S V)
    exact h1.sub h2
  · simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, dotProduct_coordRows_gram]
    linarith [hray x]

/-- **Lemma 4.2 (Minimax extraction of a single common coordinate set, p. 22).** -/
theorem lemma_4_2_MinimaxSelection : Lemma_4_2_MinimaxSelection := by
  intro n r m hm V H hH hyp
  obtain ⟨I, hIcard, hI⟩ := SparseStack.linearization hm V H hH hyp
  exact ⟨I, hIcard, loewnerLe_of_rayleigh Iᶜ V H hH (by norm_num) hI⟩

/-- Homogenization of the unit-sphere spiky lower bound (`‖x‖ = 1 ∧ d_m(Qx) ≥ ε ⇒ ‖Xx‖ ≥ λ`). -/
private lemma homogenize_spiky_bound {n r k m : ℕ} {ε lam : ℝ} (hlam : 0 < lam)
    (Q : Matrix (Fin n) (Fin r) ℝ) (hQ : Q.transpose * Q = 1) (X : Matrix (Fin k) (Fin r) ℝ)
    (hyp : ∀ x : Fin r → ℝ, vecSqNorm x = 1 → ε ^ 2 ≤ distSparseSq m (Q.mulVec x) →
      lam ^ 2 ≤ vecSqNorm (X.mulVec x)) :
    ∀ x : Fin r → ℝ, distSparseSq m (Q.mulVec x) ≤
      ε ^ 2 * vecSqNorm x + (lam ^ 2)⁻¹ * vecSqNorm (X.mulVec x) := by
  intro x
  have hl : 0 < lam ^ 2 := sq_pos_of_pos hlam
  simp only [vecSqNorm_eq_sqNorm, distSparseSq_eq] at hyp ⊢
  have hN : 0 ≤ SparseStack.sqNorm (X.mulVec x) := SparseStack.Lin.sqNorm_nonneg_aux _
  have hlN : 0 ≤ (lam ^ 2)⁻¹ * SparseStack.sqNorm (X.mulVec x) :=
    mul_nonneg (inv_nonneg.mpr hl.le) hN
  rcases (SparseStack.Lin.sqNorm_nonneg_aux x).eq_or_lt with h0 | hpos
  · have h := SparseStack.Lin.distSparseSq_le_sqNorm_aux m (Q.mulVec x)
    rw [SparseStack.Lin.sqNorm_mulVec_of_isometry Q hQ x, ← h0] at h
    rw [← h0]
    linarith
  · set c : ℝ := (Real.sqrt (SparseStack.sqNorm x))⁻¹
    have hc2 : c ^ 2 * SparseStack.sqNorm x = 1 := by
      simp only [c]
      rw [inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
    have hc2pos : 0 < c ^ 2 := by
      simp only [c]
      have : 0 < Real.sqrt (SparseStack.sqNorm x) := Real.sqrt_pos.mpr hpos
      positivity
    have hy : SparseStack.sqNorm (c • x) = 1 := by
      rw [SparseStack.Lin.sqNorm_smul_aux, hc2]
    have hdy : SparseStack.distSparseSq m (Q.mulVec (c • x)) =
        c ^ 2 * SparseStack.distSparseSq m (Q.mulVec x) := by
      rw [Matrix.mulVec_smul, SparseStack.Lin.distSparseSq_smul_aux]
    have hXy : SparseStack.sqNorm (X.mulVec (c • x)) = c ^ 2 * SparseStack.sqNorm (X.mulVec x) := by
      rw [Matrix.mulVec_smul, SparseStack.Lin.sqNorm_smul_aux]
    by_cases hbig : ε ^ 2 ≤ SparseStack.distSparseSq m (Q.mulVec (c • x))
    · have hly := hyp (c • x) hy hbig
      rw [hXy] at hly
      have hd1 : SparseStack.distSparseSq m (Q.mulVec (c • x)) ≤ 1 := by
        have h := SparseStack.Lin.distSparseSq_le_sqNorm_aux m (Q.mulVec (c • x))
        rwa [SparseStack.Lin.sqNorm_mulVec_of_isometry Q hQ, hy] at h
      rw [hdy] at hd1
      have hkey : lam ^ 2 * SparseStack.distSparseSq m (Q.mulVec x) ≤
          SparseStack.sqNorm (X.mulVec x) := by
        have hmul := mul_le_mul_of_nonneg_left hd1 hl.le
        have h1 : c ^ 2 * (lam ^ 2 * SparseStack.distSparseSq m (Q.mulVec x)) ≤
            c ^ 2 * SparseStack.sqNorm (X.mulVec x) := by
          nlinarith [hmul, hly]
        exact le_of_mul_le_mul_left h1 hc2pos
      have hD : SparseStack.distSparseSq m (Q.mulVec x) ≤
          (lam ^ 2)⁻¹ * SparseStack.sqNorm (X.mulVec x) := by
        rw [inv_mul_eq_div, le_div_iff₀ hl]
        linarith
      have hP : 0 ≤ ε ^ 2 * SparseStack.sqNorm x := by positivity
      linarith
    · push Not at hbig
      rw [hdy] at hbig
      have hDP : SparseStack.distSparseSq m (Q.mulVec x) =
          (c ^ 2 * SparseStack.distSparseSq m (Q.mulVec x)) * SparseStack.sqNorm x := by
        calc SparseStack.distSparseSq m (Q.mulVec x)
            = SparseStack.distSparseSq m (Q.mulVec x) * (c ^ 2 * SparseStack.sqNorm x) := by
              rw [hc2, mul_one]
          _ = (c ^ 2 * SparseStack.distSparseSq m (Q.mulVec x)) * SparseStack.sqNorm x := by ring
      have hsm : (c ^ 2 * SparseStack.distSparseSq m (Q.mulVec x)) * SparseStack.sqNorm x ≤
          ε ^ 2 * SparseStack.sqNorm x :=
        mul_le_mul_of_nonneg_right hbig.le hpos.le
      linarith

/-- **Theorem 2.2 (Common support extraction for spiky vectors, pp. 8, 22).** -/
theorem theorem_2_2_CommonSupport : Theorem_2_2_CommonSupport := by
  intro n r k m ε lam hm _hε hlam Q X hQ hyp
  set H : Matrix (Fin r) (Fin r) ℝ :=
    (ε ^ 2) • (1 : Matrix (Fin r) (Fin r) ℝ) + (lam ^ 2)⁻¹ • (X.transpose * X)
  have hHpsd : H.PosSemidef := by
    have h1 : ((ε ^ 2) • (1 : Matrix (Fin r) (Fin r) ℝ)).PosSemidef :=
      Matrix.PosSemidef.one.smul (sq_nonneg ε)
    have h2 : (X.transpose * X).PosSemidef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_conjTranspose_mul_self X
    exact h1.add (h2.smul (inv_nonneg.mpr (sq_nonneg lam)))
  have hHx : ∀ x : Fin r → ℝ,
      dotProduct x (H.mulVec x) =
        ε ^ 2 * vecSqNorm x + (lam ^ 2)⁻¹ * vecSqNorm (X.mulVec x) := by
    intro x
    have hXX : dotProduct x ((X.transpose * X).mulVec x) = vecSqNorm (X.mulVec x) := by
      rw [vecSqNorm_eq_sqNorm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
      rfl
    rw [vecSqNorm_eq_sqNorm x, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hXX]
    rfl
  have hhom := homogenize_spiky_bound hlam Q hQ X hyp
  have hlin : ∀ x : Fin r → ℝ, distSparseSq m (Q.mulVec x) ≤ dotProduct x (H.mulVec x) := by
    intro x
    rw [hHx]
    exact hhom x
  obtain ⟨I, hIcard, hILoew⟩ := lemma_4_2_MinimaxSelection n r m hm Q H hHpsd hlin
  refine ⟨I, hIcard, ?_⟩
  have hH_smul : (8 / 3 : ℝ) • H =
      ((8 / 3 : ℝ) * ε ^ 2) • (1 : Matrix (Fin r) (Fin r) ℝ) +
        ((8 / (3 * lam ^ 2) : ℝ) • (X.transpose * X)) := by
    simp only [H, smul_add, smul_smul]
    congr 2
    ring
  rwa [hH_smul] at hILoew

end Osi.UpperBound
