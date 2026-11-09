import Osi.Spec
import Osi.Prelim.SubspaceSing
import Osi.Prelim.Hypergeom

/-!
# Section 10.1: Coordinate-Subspace Minimax Reduction (`Lemma 10.1`)

Proves `Lemma_10_1_CoordinateSubspaceReduction`: finite-average Fubini over `R ∈ ([n] choose r)`
combined with Markov's inequality on `E[frobSq (M ω)] = n` (`IsIsotropic`) and `SatisfiesOverlapWhp`.
-/

namespace Osi.LowerBound

open Osi.Spec

private lemma frobSq_nonneg {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    0 ≤ frobSq A := by
  unfold frobSq
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma measureReal_frobSq_compl_le
    {Ω_prob : Type} [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob)
    [MeasureTheory.IsProbabilityMeasure P] {n k : ℕ} (hn : 1 ≤ n)
    {M : Ω_prob → Matrix (Fin n) (Fin k) ℝ} (hIso : IsIsotropic P M) :
    P.real {ω : Ω_prob | frobSq (M ω) ≤ 10 * (n : ℝ)}ᶜ ≤ 1 / 10 := by
  obtain ⟨hf_int, hf_exp⟩ := Osi.Prelim.expected_frobSq_of_isIsotropic hIso
  have hf_nonneg : 0 ≤ᵐ[P] (fun ω => frobSq (M ω)) :=
    Filter.Eventually.of_forall fun ω => frobSq_nonneg (M ω)
  have hmarkov :=
    MeasureTheory.mul_meas_ge_le_integral_of_nonneg hf_nonneg hf_int (10 * (n : ℝ))
  rw [hf_exp] at hmarkov
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hge_le : P.real {ω : Ω_prob | 10 * (n : ℝ) ≤ frobSq (M ω)} ≤ 1 / 10 := by
    have hmul :
        (n : ℝ) * (10 * P.real {ω : Ω_prob | 10 * (n : ℝ) ≤ frobSq (M ω)}) ≤
          (n : ℝ) * 1 := by
      calc (n : ℝ) * (10 * P.real {ω : Ω_prob | 10 * (n : ℝ) ≤ frobSq (M ω)})
          = (10 * (n : ℝ)) * P.real {ω : Ω_prob | 10 * (n : ℝ) ≤ frobSq (M ω)} := by ring
        _ ≤ (n : ℝ) := hmarkov
        _ = (n : ℝ) * 1 := (mul_one _).symm
    have h10 : 10 * P.real {ω : Ω_prob | 10 * (n : ℝ) ≤ frobSq (M ω)} ≤ 1 :=
      le_of_mul_le_mul_left hmul hn_pos
    linarith
  have hsub :
      {ω : Ω_prob | frobSq (M ω) ≤ 10 * (n : ℝ)}ᶜ ⊆
        {ω : Ω_prob | 10 * (n : ℝ) ≤ frobSq (M ω)} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
    exact hω.le
  exact (MeasureTheory.measureReal_mono hsub).trans hge_le

private lemma measureReal_good_compl_le
    {Ω_prob : Type} [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob)
    [MeasureTheory.IsProbabilityMeasure P] {n k : ℕ} (hn : 1 ≤ n) {η : ℝ}
    {M : Ω_prob → Matrix (Fin n) (Fin k) ℝ}
    (hM : IsRandomMatrix M) (hIso : IsIsotropic P M)
    (hOv : SatisfiesOverlapWhp P M η (9 / 10)) :
    P.real ({ω : Ω_prob | frobSq (M ω) ≤ 10 * (n : ℝ)} ∩
        {ω : Ω_prob | SatisfiesOverlapCond (M ω) η})ᶜ ≤ 1 / 5 := by
  set E_frob : Set Ω_prob := {ω : Ω_prob | frobSq (M ω) ≤ 10 * (n : ℝ)}
  set E_ov : Set Ω_prob := {ω : Ω_prob | SatisfiesOverlapCond (M ω) η}
  have hfrob : P.real E_frobᶜ ≤ 1 / 10 := measureReal_frobSq_compl_le P hn hIso
  have hMeas_ov : MeasurableSet E_ov := Osi.Prelim.measurableSet_satisfiesOverlapCond hM η
  have hov_ge : 9 / 10 ≤ P.real E_ov := by
    rw [MeasureTheory.measureReal_def]
    exact hOv
  have hov : P.real E_ovᶜ ≤ 1 / 10 := by
    rw [MeasureTheory.probReal_compl_eq_one_sub hMeas_ov]
    linarith
  rw [Set.compl_inter]
  exact (MeasureTheory.measureReal_union_le E_frobᶜ E_ovᶜ).trans (by linarith)

private lemma sum_indicator_coordFrame_eq
    {Ω_prob : Type} {n k r : ℕ} (hrn : r ≤ n)
    (M : Ω_prob → Matrix (Fin n) (Fin k) ℝ) (α : ℝ) (ω : Ω_prob) :
    (∑ x ∈ ((Finset.univ : Finset (Fin n)).powersetCard r).attach,
      ({ω' : Ω_prob |
          MinEigenvalueAtLeast ((M ω').transpose *
            coordFrame x.1 (Finset.mem_powersetCard.mp x.2).2) α}).indicator
        (fun _ => (1 : ℝ)) ω) =
      uniformSubsetProb n r
        (fun R => ∀ hR : R.card = r,
          MinEigenvalueAtLeast ((M ω).transpose * coordFrame R hR) α) *
        (Nat.choose n r : ℝ) := by
  classical
  set Ω_R : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard r
  set E : Finset (Fin n) → Prop :=
    fun R => ∀ hR : R.card = r, MinEigenvalueAtLeast ((M ω).transpose * coordFrame R hR) α
  have hterm :
      ∀ x ∈ Ω_R.attach,
        ({ω' : Ω_prob |
            MinEigenvalueAtLeast ((M ω').transpose *
              coordFrame x.1 (Finset.mem_powersetCard.mp x.2).2) α}).indicator
          (fun _ => (1 : ℝ)) ω =
          if E x.1 then (1 : ℝ) else 0 := by
    intro x _
    set hRx : x.1.card = r := (Finset.mem_powersetCard.mp x.2).2
    have hiff :
        MinEigenvalueAtLeast ((M ω).transpose * coordFrame x.1 hRx) α ↔ E x.1 :=
      ⟨fun hMin _ => hMin, fun hE => hE hRx⟩
    by_cases hMin : MinEigenvalueAtLeast ((M ω).transpose * coordFrame x.1 hRx) α
    · have hmem :
          ω ∈ {ω' : Ω_prob |
            MinEigenvalueAtLeast ((M ω').transpose * coordFrame x.1 hRx) α} := hMin
      rw [Set.indicator_of_mem hmem, if_pos (hiff.mp hMin)]
    · have hnmem :
          ω ∉ {ω' : Ω_prob |
            MinEigenvalueAtLeast ((M ω').transpose * coordFrame x.1 hRx) α} := hMin
      rw [Set.indicator_of_notMem hnmem, if_neg (fun hE => hMin (hiff.mpr hE))]
  rw [Finset.sum_congr rfl hterm, Finset.sum_attach Ω_R (fun R => if E R then (1 : ℝ) else 0),
    ← Finset.natCast_card_filter E Ω_R]
  have hfinset_eq :
      (Set.toFinite {R : Finset (Fin n) | R.card = r ∧ E R}).toFinset = Ω_R.filter E := by
    ext R
    simp [Ω_R, Finset.mem_powersetCard]
  have hchoose_pos : (0 : ℝ) < (Nat.choose n r : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hrn)
  unfold uniformSubsetProb
  rw [hfinset_eq, div_mul_cancel₀ _ hchoose_pos.ne']

/-- **Lemma 10.1 (Coordinate-subspace minimax reduction, p. 45).** -/
theorem lemma_10_1_CoordinateSubspaceReduction : Lemma_10_1_CoordinateSubspaceReduction := by
  intro n r k ζ α η p_osi hr1 hrn _ _ _ hp_osi hDet Ω_prob _instMeas P hProb M hM hIso hSp hOv hOSI
  have : MeasureTheory.IsProbabilityMeasure P := hProb
  have hn1 : 1 ≤ n := hr1.trans hrn
  set C : ℝ := (Nat.choose n r : ℝ)
  have hC_pos : 0 < C := Nat.cast_pos.mpr (Nat.choose_pos hrn)
  have hC_nonneg : 0 ≤ C := hC_pos.le
  set Ω_R : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard r
  have hcard_attach : (Ω_R.attach.card : ℝ) = C := by
    simp [Ω_R, C, Finset.card_powersetCard]
  set A : {R // R ∈ Ω_R} → Set Ω_prob := fun x =>
    {ω : Ω_prob |
      MinEigenvalueAtLeast ((M ω).transpose *
        coordFrame x.1 (Finset.mem_powersetCard.mp x.2).2) α}
  have hMeas_A : ∀ x : {R // R ∈ Ω_R}, MeasurableSet (A x) := fun x =>
    Osi.Prelim.measurableSet_minEigenvalueAtLeast_mul hM
      (coordFrame x.1 (Finset.mem_powersetCard.mp x.2).2) α
  have hInt_A :
      ∀ x : {R // R ∈ Ω_R},
        MeasureTheory.Integrable ((A x).indicator (fun _ => (1 : ℝ))) P := fun x =>
    (MeasureTheory.integrable_const (1 : ℝ)).indicator (hMeas_A x)
  have hsum_lower : C * p_osi ≤ ∑ x ∈ Ω_R.attach, P.real (A x) := by
    calc C * p_osi
        = ∑ _x ∈ Ω_R.attach, p_osi := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard_attach]
      _ ≤ ∑ x ∈ Ω_R.attach, P.real (A x) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [MeasureTheory.measureReal_def]
          exact hOSI (coordFrame x.1 (Finset.mem_powersetCard.mp x.2).2)
            (Osi.Prelim.coordFrame_isIsometry x.1 (Finset.mem_powersetCard.mp x.2).2)
  have hsum_eq_int :
      (∑ x ∈ Ω_R.attach, P.real (A x)) =
        ∫ ω, (∑ x ∈ Ω_R.attach, (A x).indicator (fun _ => (1 : ℝ)) ω) ∂P := by
    rw [MeasureTheory.integral_finsetSum Ω_R.attach (fun x _ => hInt_A x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MeasureTheory.integral_indicator_const (1 : ℝ) (hMeas_A x), smul_eq_mul, mul_one]
  set G : Set Ω_prob :=
    {ω : Ω_prob | frobSq (M ω) ≤ 10 * (n : ℝ)} ∩ {ω : Ω_prob | SatisfiesOverlapCond (M ω) η}
  have hMeas_G : MeasurableSet G :=
    (Osi.Prelim.measurableSet_frobSq_le hM (10 * (n : ℝ))).inter
      (Osi.Prelim.measurableSet_satisfiesOverlapCond hM η)
  set g : Ω_prob → ℝ := fun ω => (1 / 4 : ℝ) * C + Gᶜ.indicator (fun _ => C) ω
  have hae :
      (fun ω => ∑ x ∈ Ω_R.attach, (A x).indicator (fun _ => (1 : ℝ)) ω) ≤ᵐ[P] g := by
    refine hSp.mono fun ω hω_sp => ?_
    change (∑ x ∈ Ω_R.attach, (A x).indicator (fun _ => (1 : ℝ)) ω) ≤ g ω
    by_cases hωG : ω ∈ G
    · have hnotGc : ω ∉ Gᶜ := fun h => h hωG
      have hg_val : g ω = (1 / 4 : ℝ) * C := by
        simp only [g, Set.indicator_of_notMem hnotGc, add_zero]
      rw [hg_val]
      have hsum_ω :
          (∑ x ∈ Ω_R.attach, (A x).indicator (fun _ => (1 : ℝ)) ω) =
            uniformSubsetProb n r
              (fun R => ∀ hR : R.card = r,
                MinEigenvalueAtLeast ((M ω).transpose * coordFrame R hR) α) * C :=
        sum_indicator_coordFrame_eq hrn M α ω
      rw [hsum_ω]
      exact mul_le_mul_of_nonneg_right (hDet (M ω) hω_sp hωG.1 hωG.2) hC_nonneg
    · have hGc : ω ∈ Gᶜ := hωG
      have hg_val : g ω = (1 / 4 : ℝ) * C + C := by
        simp only [g, Set.indicator_of_mem hGc]
      rw [hg_val]
      have htriv : (∑ x ∈ Ω_R.attach, (A x).indicator (fun _ => (1 : ℝ)) ω) ≤ C := by
        calc ∑ x ∈ Ω_R.attach, (A x).indicator (fun _ => (1 : ℝ)) ω
            ≤ ∑ _x ∈ Ω_R.attach, (1 : ℝ) := by
              refine Finset.sum_le_sum fun x _ => ?_
              by_cases hx : ω ∈ A x <;> simp [hx]
          _ = C := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard_attach]
      linarith
  have hInt_LHS :
      MeasureTheory.Integrable
        (fun ω => ∑ x ∈ Ω_R.attach, (A x).indicator (fun _ => (1 : ℝ)) ω) P :=
    MeasureTheory.integrable_finsetSum Ω_R.attach (fun x _ => hInt_A x)
  have hInt_const : MeasureTheory.Integrable (fun _ : Ω_prob => (1 / 4 : ℝ) * C) P :=
    MeasureTheory.integrable_const ((1 / 4 : ℝ) * C)
  have hInt_Gc : MeasureTheory.Integrable (Gᶜ.indicator (fun _ : Ω_prob => C)) P :=
    (MeasureTheory.integrable_const C).indicator hMeas_G.compl
  have hInt_g : MeasureTheory.Integrable g P := hInt_const.fun_add hInt_Gc
  have hint_le :
      (∫ ω, (∑ x ∈ Ω_R.attach, (A x).indicator (fun _ => (1 : ℝ)) ω) ∂P) ≤ ∫ ω, g ω ∂P :=
    MeasureTheory.integral_mono_ae hInt_LHS hInt_g hae
  have hint_g : (∫ ω, g ω ∂P) = (1 / 4 : ℝ) * C + P.real Gᶜ * C := by
    change (∫ ω, ((1 / 4 : ℝ) * C + Gᶜ.indicator (fun _ => C) ω) ∂P) = _
    rw [MeasureTheory.integral_add hInt_const hInt_Gc, MeasureTheory.integral_const,
      MeasureTheory.integral_indicator_const C hMeas_G.compl, MeasureTheory.probReal_univ,
      smul_eq_mul, smul_eq_mul, one_mul]
  have hGc_le : P.real Gᶜ ≤ 1 / 5 := measureReal_good_compl_le P hn1 hM hIso hOv
  have hGc_mul : P.real Gᶜ * C ≤ (1 / 5 : ℝ) * C :=
    mul_le_mul_of_nonneg_right hGc_le hC_nonneg
  have hC_bound : C * p_osi ≤ C * (9 / 20 : ℝ) := by
    calc C * p_osi
        ≤ ∑ x ∈ Ω_R.attach, P.real (A x) := hsum_lower
      _ = ∫ ω, (∑ x ∈ Ω_R.attach, (A x).indicator (fun _ => (1 : ℝ)) ω) ∂P := hsum_eq_int
      _ ≤ ∫ ω, g ω ∂P := hint_le
      _ = (1 / 4 : ℝ) * C + P.real Gᶜ * C := hint_g
      _ ≤ (1 / 4 : ℝ) * C + (1 / 5 : ℝ) * C := by linarith
      _ = C * (9 / 20 : ℝ) := by ring
  have hp_le : p_osi ≤ 9 / 20 := le_of_mul_le_mul_left hC_bound hC_pos
  linarith

end Osi.LowerBound
