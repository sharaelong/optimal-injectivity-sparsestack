import Osi.Spec
import Osi.Prelim.SubspaceSing
import Osi.Prelim.Hypergeom
import Osi.LowerBound.RowPreprocess
import Osi.LowerBound.C4Subgraph
import Osi.LowerBound.HallReservoirs
import Osi.LowerBound.CoordReduction

/-!
# Section 10.2 & Theorem 1.3: Finite-Scale Coordinate Capture and Lower-Bound Endgame

Proves `Theorem_10_2_FiniteScale`, `Theorem_1_3_LowerBound_HalfProb`, `Theorem_1_3_LowerBound`,
and `Theorem_1_3_QuadraticN`.
-/

namespace Osi.LowerBound

open Osi.Spec

private lemma log_bounds_of_exp_le {r : ℕ} {M : ℝ}
    (hM1 : Real.exp 1 ≤ M) (hrM : Real.exp M ≤ (r : ℝ)) :
    M ≤ Real.log (r : ℝ) ∧
      1 < Real.log (r : ℝ) ∧
      1 ≤ Real.log (Real.log (r : ℝ)) ∧
      1 ≤ Real.log (r : ℝ) / Real.log (Real.log (r : ℝ)) ∧
      Real.log (r : ℝ) / Real.log (Real.log (r : ℝ)) ≤ Real.log (r : ℝ) := by
  have hMt : M ≤ Real.log (r : ℝ) := by
    rw [← Real.log_exp M]
    exact Real.log_le_log (Real.exp_pos M) hrM
  have he1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
  have ht1 : 1 < Real.log (r : ℝ) := lt_of_lt_of_le (lt_of_lt_of_le he1 hM1) hMt
  have hlogt1 : 1 ≤ Real.log (Real.log (r : ℝ)) := by
    have het : Real.exp 1 ≤ Real.log (r : ℝ) := le_trans hM1 hMt
    have := Real.log_le_log (Real.exp_pos 1) het
    rwa [Real.log_exp] at this
  have hlogt_lt : Real.log (Real.log (r : ℝ)) ≤ Real.log (r : ℝ) := by
    have := Real.log_le_sub_one_of_pos (lt_trans zero_lt_one ht1)
    linarith
  have hlogt_pos : 0 < Real.log (Real.log (r : ℝ)) := lt_of_lt_of_le zero_lt_one hlogt1
  exact ⟨hMt, ht1, hlogt1, (one_le_div hlogt_pos).mpr hlogt_lt,
    div_le_self (le_of_lt (lt_trans zero_lt_one ht1)) hlogt1⟩

private lemma prob_le_quarter_of_small_or_one {n r k : ℕ} {α : ℝ}
    {S : Matrix (Fin n) (Fin k) ℝ} (hrn : r ≤ n)
    (h910 : (9 / 10 : ℝ) ≤ uniformSubsetProb n r
      (fun R => ∀ hR : R.card = r, ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α)) :
    uniformSubsetProb n r
      (fun R => ∀ hR : R.card = r, MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α) ≤
      1 / 4 := by
  let E : Finset (Fin n) → Prop :=
    fun R => ∀ hR : R.card = r, MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α
  have hmono : uniformSubsetProb n r
      (fun R => ∀ hR : R.card = r, ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α) ≤
      uniformSubsetProb n r (fun R => ¬ E R) := by
    refine Osi.Prelim.uniformSubsetProb_mono ?_
    intro R hR hneg hpos
    exact hneg hR (hpos hR)
  have hcompl := Osi.Prelim.uniformSubsetProb_compl hrn E
  linarith

private lemma zero_sparsity_capture {n r k : ℕ} {α : ℝ} {S : Matrix (Fin n) (Fin k) ℝ}
    (hr : 3 ≤ r) (hα : 0 < α) (h0 : ∀ i : Fin n, (rowSupport S i).card ≤ 0) :
    uniformSubsetProb n r
      (fun R => ∀ hR : R.card = r, MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α) ≤
      1 / 4 := by
  have hS0 : S = 0 := by
    ext i j
    by_contra hij
    have hmem : j ∈ rowSupport S i := (Set.Finite.mem_toFinset _).mpr hij
    have hemp : rowSupport S i = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (h0 i))
    simp [hemp] at hmem
  have hnot : ∀ R : Finset (Fin n), R.card = r →
      ¬ (∀ hR : R.card = r, MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α) := by
    intro R hR hall
    have hmin := hall hR
    rw [hS0, Matrix.transpose_zero, Matrix.zero_mul] at hmin
    let x : Fin r → ℝ := fun _ => 1
    have hx_norm : vecSqNorm x = (r : ℝ) := by simp [vecSqNorm, x]
    have hx_pos : 0 < vecSqNorm x := by
      rw [hx_norm]
      exact Nat.cast_pos.mpr (by omega)
    have hAx : vecSqNorm ((0 : Matrix (Fin k) (Fin r) ℝ).mulVec x) = 0 := by
      simp [vecSqNorm]
    refine Osi.Prelim.not_minEigenvalueAtLeast_of_witness 0 α x hx_pos ?_ hmin
    rw [hAx]
    exact mul_pos hα hx_pos
  have hemp_set : (Set.toFinite {R : Finset (Fin n) | R.card = r ∧
      ∀ hR : R.card = r, MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α}).toFinset = ∅ := by
    ext R
    simp only [Set.Finite.mem_toFinset, Finset.notMem_empty, iff_false]
    rintro ⟨hR, hall⟩
    exact hnot R hR hall
  unfold uniformSubsetProb
  rw [hemp_set]
  norm_num

private lemma one_sparsity_small_or_one {n k : ℕ} {α : ℝ} {S : Matrix (Fin n) (Fin k) ℝ}
    (hn : 1 ≤ n) (hα : 0 < α) (h1 : ∀ i : Fin n, (rowSupport S i).card ≤ 1) :
    (n : ℝ) / 16 ≤ (smallRows S α).card ∨ (n : ℝ) / 16 ≤ (oneSparseRows S).card := by
  have huniv : (Finset.univ : Finset (Fin n)) ⊆ smallRows S α ∪ oneSparseRows S := by
    intro i _
    have hcard := h1 i
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with hc0 | hc1
    · refine Finset.mem_union.mpr (Or.inl ?_)
      rw [smallRows, Set.Finite.mem_toFinset]
      change vecSqNorm (S i) < α
      have hrow0 : ∀ j : Fin k, S i j = 0 := by
        intro j
        by_contra hij
        have hmem : j ∈ rowSupport S i := (Set.Finite.mem_toFinset _).mpr hij
        rw [Finset.card_eq_zero.mp hc0] at hmem
        simp at hmem
      have hsq0 : vecSqNorm (S i) = 0 := by simp [vecSqNorm, hrow0]
      linarith
    · refine Finset.mem_union.mpr (Or.inr ?_)
      rw [oneSparseRows, Set.Finite.mem_toFinset]
      exact hc1
  have hcard_le : n ≤ (smallRows S α).card + (oneSparseRows S).card := by
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (smallRows S α ∪ oneSparseRows S).card := Finset.card_le_card huniv
      _ ≤ (smallRows S α).card + (oneSparseRows S).card := Finset.card_union_le _ _
  have hcast : (n : ℝ) ≤ ((smallRows S α).card : ℝ) + ((oneSparseRows S).card : ℝ) := by
    exact_mod_cast hcard_le
  have hn_pos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  by_contra hneg
  have hneg1 : ¬ (n : ℝ) / 16 ≤ (smallRows S α).card := fun h => hneg (Or.inl h)
  have hneg2 : ¬ (n : ℝ) / 16 ≤ (oneSparseRows S).card := fun h => hneg (Or.inr h)
  linarith

private lemma cleanRows_card_ge_of_not_elim {n k : ℕ} {α : ℝ} {S : Matrix (Fin n) (Fin k) ℝ}
    (hfrob : frobSq S ≤ 10 * (n : ℝ))
    (hnot : ¬ ((n : ℝ) / 16 ≤ (smallRows S α).card ∨ (n : ℝ) / 16 ≤ (oneSparseRows S).card)) :
    (13 / 16 : ℝ) * (n : ℝ) ≤ ((cleanRows S α 160).card : ℝ) := by
  have hnot1 : ¬ (n : ℝ) / 16 ≤ (smallRows S α).card := fun h => hnot (Or.inl h)
  have hnot2 : ¬ (n : ℝ) / 16 ≤ (oneSparseRows S).card := fun h => hnot (Or.inr h)
  have hheavy : ((heavyRows S 160).card : ℝ) ≤ (n : ℝ) / 16 :=
    lemma_8_1_HeavyRowCount n k S hfrob
  let U : Finset (Fin n) := heavyRows S 160 ∪ smallRows S α ∪ oneSparseRows S
  have hU : U.card ≤ (heavyRows S 160).card + (smallRows S α).card + (oneSparseRows S).card := by
    calc U.card ≤ (heavyRows S 160 ∪ smallRows S α).card + (oneSparseRows S).card :=
          Finset.card_union_le _ _
      _ ≤ (heavyRows S 160).card + (smallRows S α).card + (oneSparseRows S).card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
  have huniv : n ≤ (cleanRows S α 160).card + U.card := by
    have := Finset.card_le_card_sdiff_add_card (s := (Finset.univ : Finset (Fin n))) (t := U)
    simpa [cleanRows, U] using this
  have hnat : n ≤ (cleanRows S α 160).card +
      ((heavyRows S 160).card + (smallRows S α).card + (oneSparseRows S).card) :=
    le_trans huniv (Nat.add_le_add_left hU _)
  have hreal : (n : ℝ) ≤ ((cleanRows S α 160).card : ℝ) +
      (((heavyRows S 160).card : ℝ) + ((smallRows S α).card : ℝ) + ((oneSparseRows S).card : ℝ)) := by
    exact_mod_cast hnat
  linarith

private lemma samp_size_bounds {α C_samp C_n c L_ratio : ℝ} {n r ζ n₀ : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1) (hCsamp : 1024 ≤ C_samp)
    (hCn : C_samp / α + 1 ≤ C_n) (hr3 : 3 ≤ r) (hζ2 : 2 ≤ ζ)
    (hL1 : 1 ≤ L_ratio) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hζ_le : (ζ : ℝ) ≤ c * Real.sqrt L_ratio)
    (hn_ge : C_n * (r : ℝ) * L_ratio ^ 3 ≤ (n : ℝ))
    (hn₀_eq : n₀ = Nat.ceil (C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α)) :
    r ≤ n₀ ∧ n₀ ≤ n ∧ (n₀ : ℝ) ≤ (C_samp / α + 1) * (r : ℝ) * L_ratio ^ 3 := by
  have hr_pos : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
  have hζ_real : (2 : ℝ) ≤ (ζ : ℝ) := by exact_mod_cast hζ2
  have hL0 : 0 ≤ L_ratio := le_trans zero_le_one hL1
  have hζ_sq : (ζ : ℝ) ^ 2 ≤ L_ratio := by
    have h1 : (ζ : ℝ) ^ 2 ≤ (c * Real.sqrt L_ratio) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg ζ) hζ_le 2
    rw [mul_pow, Real.sq_sqrt hL0] at h1
    have h2 : c ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hζ6 : (ζ : ℝ) ^ 6 ≤ L_ratio ^ 3 := by
    calc (ζ : ℝ) ^ 6 = ((ζ : ℝ) ^ 2) ^ 3 := by ring
      _ ≤ L_ratio ^ 3 := pow_le_pow_left₀ (sq_nonneg _) hζ_sq 3
  have harg_nonneg : 0 ≤ C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α := by positivity
  have hr_le_n0 : r ≤ n₀ := by
    have hζ6_ge : (1 : ℝ) ≤ (ζ : ℝ) ^ 6 := one_le_pow₀ (by linarith)
    have hdiv_ge : 1 ≤ C_samp / α := by
      rw [one_le_div hα0]
      linarith
    have hr_le_arg : (r : ℝ) ≤ C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α := by
      have : (r : ℝ) * 1 * 1 ≤ (r : ℝ) * (C_samp / α) * (ζ : ℝ) ^ 6 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdiv_ge (by positivity)) hζ6_ge zero_le_one (by positivity)
      linarith [show C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α = (r : ℝ) * (C_samp / α) * (ζ : ℝ) ^ 6 by ring]
    have hceil := le_trans hr_le_arg (Nat.le_ceil _)
    rw [← hn₀_eq] at hceil
    exact_mod_cast hceil
  have hn0_upper : (n₀ : ℝ) ≤ (C_samp / α + 1) * (r : ℝ) * L_ratio ^ 3 := by
    have hceil_lt : (n₀ : ℝ) ≤ C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α + 1 := by
      rw [hn₀_eq]
      exact le_of_lt (Nat.ceil_lt_add_one harg_nonneg)
    have hterm1 : C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α ≤ (C_samp / α) * (r : ℝ) * L_ratio ^ 3 := by
      have : (C_samp / α) * (r : ℝ) * (ζ : ℝ) ^ 6 ≤ (C_samp / α) * (r : ℝ) * L_ratio ^ 3 :=
        mul_le_mul_of_nonneg_left hζ6 (by positivity)
      linarith [show C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α = (C_samp / α) * (r : ℝ) * (ζ : ℝ) ^ 6 by ring]
    have h1_le : 1 ≤ (r : ℝ) * L_ratio ^ 3 := by
      have : (1 : ℝ) ≤ L_ratio ^ 3 := one_le_pow₀ hL1
      nlinarith
    linarith
  have hn0_le_n : n₀ ≤ n := by
    have h1 : (C_samp / α + 1) * (r : ℝ) * L_ratio ^ 3 ≤ C_n * (r : ℝ) * L_ratio ^ 3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCn (by positivity)) (by positivity)
    have h2 : (n₀ : ℝ) ≤ (n : ℝ) := le_trans hn0_upper (le_trans h1 hn_ge)
    exact_mod_cast h2
  exact ⟨hr_le_n0, hn0_le_n, hn0_upper⟩

private lemma tree_size_and_rate_bounds {α C_samp c_T : ℝ} {r ζ n₀ T : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1) (hc_T : 0 < c_T) (hCsamp : 1024 ≤ C_samp)
    (hr3 : 3 ≤ r) (hζ2 : 2 ≤ ζ)
    (hr_exp : Real.exp
      (max (Real.exp 1) (max (4 * (642 / α)) (max (2 * (C_samp / α + 1)) (368640 / c_T)))) ≤ (r : ℝ))
    (hζ_le : (ζ : ℝ) ≤ (α / 6000) * Real.sqrt (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))))
    (hn₀_eq : n₀ = Nat.ceil (C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α))
    (hT_ge : c_T * (r : ℝ) / (ζ : ℝ) ^ 5 ≤ (T : ℝ)) :
    let q : ℕ := Nat.ceil (640 * (ζ : ℝ) / α)
    let B : ℕ := 1 + ζ * q
    2 * B ≤ r ∧ 8 ≤ (T : ℝ) * ((r : ℝ) / (2 * (n₀ : ℝ))) ^ B := by
  intro q B
  let A₂ : ℝ := 642 / α
  let c : ℝ := α / 6000
  let M_log : ℝ := max (Real.exp 1) (max (4 * A₂) (max (2 * (C_samp / α + 1)) (368640 / c_T)))
  let t : ℝ := Real.log (r : ℝ)
  let L_ratio : ℝ := t / Real.log t
  have hM1 : Real.exp 1 ≤ M_log := le_max_left _ _
  obtain ⟨hMt, ht1, hlogt1, hL1, hLt⟩ := log_bounds_of_exp_le hM1 hr_exp
  have hM_rest : max (4 * A₂) (max (2 * (C_samp / α + 1)) (368640 / c_T)) ≤ t :=
    le_trans (le_max_right _ _) hMt
  have ht_A2 : 4 * A₂ ≤ t := le_trans (le_max_left _ _) hM_rest
  have ht_Csamp : 2 * (C_samp / α + 1) ≤ t :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hM_rest)
  have ht_cT : 368640 / c_T ≤ t :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hM_rest)
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hexp_t : Real.exp t = (r : ℝ) := Real.exp_log hr_pos
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    change α / 6000 ≤ 1
    linarith
  have hL0 : 0 ≤ L_ratio := le_trans zero_le_one hL1
  have hζ_real : (2 : ℝ) ≤ (ζ : ℝ) := by exact_mod_cast hζ2
  have hζ_sq_c : (ζ : ℝ) ^ 2 ≤ c ^ 2 * L_ratio := by
    have h1 : (ζ : ℝ) ^ 2 ≤ (c * Real.sqrt L_ratio) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg ζ) hζ_le 2
    rwa [mul_pow, Real.sq_sqrt hL0] at h1
  have hζ_sq_L : (ζ : ℝ) ^ 2 ≤ L_ratio := by
    have : c ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hζ_sq_t : (ζ : ℝ) ^ 2 ≤ t := le_trans hζ_sq_L hLt
  have hζ_le_t : (ζ : ℝ) ≤ t := by nlinarith
  have hB_bound : (B : ℝ) ≤ A₂ * (ζ : ℝ) ^ 2 := by
    have hq_le : (q : ℝ) ≤ 640 * (ζ : ℝ) / α + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (by positivity))
    have h1_div : 1 ≤ (ζ : ℝ) / α := (one_le_div hα0).mpr (by linarith)
    have h1_sq_div : 1 ≤ (ζ : ℝ) ^ 2 / α := (one_le_div hα0).mpr (by nlinarith)
    have hq_le2 : (q : ℝ) ≤ 641 * (ζ : ℝ) / α := by
      linarith [show 641 * (ζ : ℝ) / α = 640 * (ζ : ℝ) / α + (ζ : ℝ) / α by ring]
    have hB_eq : (B : ℝ) = 1 + (ζ : ℝ) * (q : ℝ) := by exact_mod_cast rfl
    have hmul : (ζ : ℝ) * (q : ℝ) ≤ 641 * (ζ : ℝ) ^ 2 / α := by
      have := mul_le_mul_of_nonneg_left hq_le2 (Nat.cast_nonneg ζ)
      linarith [show (ζ : ℝ) * (641 * (ζ : ℝ) / α) = 641 * (ζ : ℝ) ^ 2 / α by ring]
    change (B : ℝ) ≤ (642 / α) * (ζ : ℝ) ^ 2
    linarith [show (642 / α) * (ζ : ℝ) ^ 2 = 641 * (ζ : ℝ) ^ 2 / α + (ζ : ℝ) ^ 2 / α by ring]
  have h2B_le_r : 2 * B ≤ r := by
    have hA2_pos : 0 < A₂ := by positivity
    have hBt : (B : ℝ) ≤ A₂ * t := le_trans hB_bound (mul_le_mul_of_nonneg_left hζ_sq_t hA2_pos.le)
    have h_exp2 := Real.pow_div_factorial_le_exp t (le_of_lt (lt_trans zero_lt_one ht1)) 2
    rw [hexp_t] at h_exp2
    have ht2_le : t ^ 2 ≤ 2 * (r : ℝ) := by
      norm_num [Nat.factorial] at h_exp2
      linarith
    have h2B_real : (2 : ℝ) * (B : ℝ) ≤ (r : ℝ) := by
      nlinarith [ht_A2, hBt, ht2_le, hA2_pos]
    exact_mod_cast h2B_real
  -- Bound n₀ and u = 2 n₀ / r
  obtain ⟨hr_le_n0, -, hn0_upper⟩ := samp_size_bounds hα0 hα1 hCsamp (le_refl _) hr3 hζ2 hL1
    hc0 hc1 hζ_le (n := Nat.ceil ((C_samp / α + 1) * (r : ℝ) * L_ratio ^ 3))
    (Nat.le_ceil _) hn₀_eq
  have hn0_pos : 0 < (n₀ : ℝ) := by exact_mod_cast (show 0 < n₀ by omega)
  let u : ℝ := 2 * (n₀ : ℝ) / (r : ℝ)
  have hu_ge_2 : 2 ≤ u := by
    have hr_n0_real : (r : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hr_le_n0
    exact (le_div_iff₀ hr_pos).mpr (by linarith)
  have hu_pos : 0 < u := by linarith
  have hu_le_t4 : u ≤ t ^ 4 := by
    have hL3_t3 : L_ratio ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ hL0 hLt 3
    have hn0_t3 : (n₀ : ℝ) ≤ (C_samp / α + 1) * (r : ℝ) * t ^ 3 :=
      le_trans hn0_upper (mul_le_mul_of_nonneg_left hL3_t3 (by positivity))
    have hu_le1 : u ≤ 2 * (C_samp / α + 1) * t ^ 3 := by
      rw [div_le_iff₀ hr_pos]
      linarith
    have ht3_nonneg : 0 ≤ t ^ 3 := by positivity
    calc u ≤ 2 * (C_samp / α + 1) * t ^ 3 := hu_le1
      _ ≤ t * t ^ 3 := mul_le_mul_of_nonneg_right ht_Csamp ht3_nonneg
      _ = t ^ 4 := by ring
  have hu_pow_le : u ^ B ≤ Real.exp (t / 2) := by
    have hlog_u_nonneg : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
    have hlog_u_le : Real.log u ≤ 4 * Real.log t := by
      have := Real.log_le_log hu_pos hu_le_t4
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    have hBc : (B : ℝ) ≤ A₂ * c ^ 2 * L_ratio := by
      have hA2_pos : 0 ≤ A₂ := by positivity
      calc (B : ℝ) ≤ A₂ * (ζ : ℝ) ^ 2 := hB_bound
        _ ≤ A₂ * (c ^ 2 * L_ratio) := mul_le_mul_of_nonneg_left hζ_sq_c hA2_pos
        _ = A₂ * c ^ 2 * L_ratio := by ring
    have h4A2c2 : 4 * A₂ * c ^ 2 ≤ 1 / 2 := by
      have h_eq : 4 * A₂ * c ^ 2 = (2568 / 36000000) * α := by
        simp only [A₂, c]
        field_simp
        ring
      rw [h_eq]
      linarith
    have hBlogu : (B : ℝ) * Real.log u ≤ t / 2 := by
      have hlogt_ne : Real.log t ≠ 0 := by linarith
      calc (B : ℝ) * Real.log u
          ≤ (A₂ * c ^ 2 * L_ratio) * (4 * Real.log t) :=
            mul_le_mul hBc hlog_u_le hlog_u_nonneg (by positivity)
        _ = (4 * A₂ * c ^ 2) * t := by
            simp only [L_ratio]
            field_simp
        _ ≤ (1 / 2) * t := mul_le_mul_of_nonneg_right h4A2c2 (by linarith)
        _ = t / 2 := by ring
    calc u ^ B = (Real.exp (Real.log u)) ^ B := by rw [Real.exp_log hu_pos]
      _ = Real.exp ((B : ℝ) * Real.log u) := (Real.exp_nat_mul (Real.log u) B).symm
      _ ≤ Real.exp (t / 2) := Real.exp_le_exp.mpr hBlogu
  -- Bound T ≥ 8 exp(t / 2)
  have hT_exp : 8 * Real.exp (t / 2) ≤ (T : ℝ) := by
    have ht_half_nonneg : 0 ≤ t / 2 := by linarith
    have hexp6 := Real.pow_div_factorial_le_exp (t / 2) ht_half_nonneg 6
    have ht6_le : t ^ 6 ≤ 46080 * Real.exp (t / 2) := by
      norm_num [Nat.factorial] at hexp6
      linarith
    have hexp_sq : Real.exp (t / 2) * Real.exp (t / 2) = (r : ℝ) := by
      rw [← Real.exp_add, add_halves, hexp_t]
    have ht6_exp : t ^ 6 * Real.exp (t / 2) ≤ 46080 * (r : ℝ) := by
      have := mul_le_mul_of_nonneg_right ht6_le (Real.exp_nonneg (t / 2))
      linarith
    have hcT_t : 368640 ≤ t * c_T := (div_le_iff₀ hc_T).mp ht_cT
    have h8_t5 : 8 * t ^ 5 * Real.exp (t / 2) ≤ c_T * (r : ℝ) := by
      have ht5_pos : 0 ≤ t ^ 5 * Real.exp (t / 2) := by positivity
      have h1 : 368640 * (t ^ 5 * Real.exp (t / 2)) ≤ (t * c_T) * (t ^ 5 * Real.exp (t / 2)) :=
        mul_le_mul_of_nonneg_right hcT_t ht5_pos
      have h2 : (t * c_T) * (t ^ 5 * Real.exp (t / 2)) = c_T * (t ^ 6 * Real.exp (t / 2)) := by ring
      have h3 : c_T * (t ^ 6 * Real.exp (t / 2)) ≤ c_T * (46080 * (r : ℝ)) :=
        mul_le_mul_of_nonneg_left ht6_exp hc_T.le
      linarith
    have hζ5_le : (ζ : ℝ) ^ 5 ≤ t ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg ζ) hζ_le_t 5
    have hζ5_pos : 0 < (ζ : ℝ) ^ 5 := by positivity
    have h8_ζ5 : 8 * (ζ : ℝ) ^ 5 * Real.exp (t / 2) ≤ c_T * (r : ℝ) := by
      have : 8 * (ζ : ℝ) ^ 5 * Real.exp (t / 2) ≤ 8 * t ^ 5 * Real.exp (t / 2) := by
        have := mul_le_mul_of_nonneg_right hζ5_le (Real.exp_nonneg (t / 2))
        linarith
      linarith
    have hdiv : 8 * Real.exp (t / 2) ≤ c_T * (r : ℝ) / (ζ : ℝ) ^ 5 := by
      rw [le_div_iff₀ hζ5_pos]
      linarith
    exact le_trans hdiv hT_ge
  have h8_uB : 8 * u ^ B ≤ (T : ℝ) := le_trans (mul_le_mul_of_nonneg_left hu_pow_le (by positivity)) hT_exp
  have hrate : 8 ≤ (T : ℝ) * ((r : ℝ) / (2 * (n₀ : ℝ))) ^ B := by
    have hinv_pos : 0 ≤ ((r : ℝ) / (2 * (n₀ : ℝ))) ^ B := by positivity
    have hmul := mul_le_mul_of_nonneg_right h8_uB hinv_pos
    have hcancel : u ^ B * ((r : ℝ) / (2 * (n₀ : ℝ))) ^ B = 1 := by
      rw [← mul_pow]
      have hbase : u * ((r : ℝ) / (2 * (n₀ : ℝ))) = 1 := by
        simp only [u]
        field_simp
      rw [hbase, one_pow]
    linarith
  exact ⟨h2B_le_r, hrate⟩

private lemma two_stage_good_bad_combine {n n₀ r : ℕ}
    (hr : r ≤ n₀) (hn₀ : n₀ ≤ n)
    (GoodV0 E : Finset (Fin n) → Prop)
    (hgood_prob : (7 / 8 : ℝ) ≤ uniformSubsetProb n n₀ GoodV0)
    (hgood_cond : ∀ V₀ : Finset (Fin n), V₀.card = n₀ → GoodV0 V₀ →
      (((Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ E R}).toFinset).card : ℝ) /
        (Nat.choose n₀ r : ℝ) ≤ 1 / 8) :
    uniformSubsetProb n r E ≤ 1 / 4 := by
  let P_n0 : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard n₀
  let G_fin : Finset (Finset (Fin n)) :=
    (Set.toFinite {V₀ : Finset (Fin n) | V₀.card = n₀ ∧ GoodV0 V₀}).toFinset
  let cond : Finset (Fin n) → ℝ := fun V₀ =>
    (((Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ E R}).toFinset).card : ℝ) /
      (Nat.choose n₀ r : ℝ)
  have hP_card : P_n0.card = Nat.choose n n₀ := by simp [P_n0]
  have hchoose_n0_pos : 0 < (Nat.choose n n₀ : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hn₀)
  have hchoose_r_pos : 0 < (Nat.choose n₀ r : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hr)
  have hG_sub : G_fin ⊆ P_n0 := by
    intro V₀ hV₀
    have h := (Set.Finite.mem_toFinset _).mp hV₀
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ V₀, h.1⟩
  have hG_card_ge : (7 / 8 : ℝ) * (Nat.choose n n₀ : ℝ) ≤ (G_fin.card : ℝ) := by
    unfold uniformSubsetProb at hgood_prob
    rwa [le_div_iff₀ hchoose_n0_pos] at hgood_prob
  have hG_card_le : (G_fin.card : ℝ) ≤ (Nat.choose n n₀ : ℝ) := by
    have := Finset.card_le_card hG_sub
    rw [hP_card] at this
    exact_mod_cast this
  have hsdiff_card : ((P_n0 \ G_fin).card : ℝ) ≤ (1 / 8 : ℝ) * (Nat.choose n n₀ : ℝ) := by
    have hadd := Finset.card_sdiff_add_card_eq_card hG_sub
    rw [hP_card] at hadd
    have hadd_real : ((P_n0 \ G_fin).card : ℝ) + (G_fin.card : ℝ) = (Nat.choose n n₀ : ℝ) := by
      exact_mod_cast hadd
    linarith
  have hcond_le_one : ∀ V₀ ∈ P_n0, cond V₀ ≤ 1 := by
    intro V₀ hV₀
    have hV0_card : V₀.card = n₀ := (Finset.mem_powersetCard.mp hV₀).2
    have hsub : (Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ E R}).toFinset ⊆
        V₀.powersetCard r := by
      intro R hR
      have h := (Set.Finite.mem_toFinset _).mp hR
      exact Finset.mem_powersetCard.mpr ⟨h.1, h.2.1⟩
    have hcard_le : ((Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ E R}).toFinset).card ≤
        Nat.choose n₀ r := by
      simpa [Finset.card_powersetCard, hV0_card] using Finset.card_le_card hsub
    have hreal_le : (((Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ E R}).toFinset).card : ℝ) ≤
        (Nat.choose n₀ r : ℝ) := by exact_mod_cast hcard_le
    exact (div_le_one hchoose_r_pos).mpr hreal_le
  have hsum_bad : ∑ V₀ ∈ P_n0 \ G_fin, cond V₀ ≤ (1 / 8 : ℝ) * (Nat.choose n n₀ : ℝ) := by
    calc ∑ V₀ ∈ P_n0 \ G_fin, cond V₀
        ≤ ∑ _V₀ ∈ P_n0 \ G_fin, (1 : ℝ) :=
          Finset.sum_le_sum (fun V₀ hV₀ => hcond_le_one V₀ (Finset.sdiff_subset hV₀))
      _ = ((P_n0 \ G_fin).card : ℝ) := by simp
      _ ≤ (1 / 8 : ℝ) * (Nat.choose n n₀ : ℝ) := hsdiff_card
  have hsum_good : ∑ V₀ ∈ G_fin, cond V₀ ≤ (1 / 8 : ℝ) * (Nat.choose n n₀ : ℝ) := by
    calc ∑ V₀ ∈ G_fin, cond V₀
        ≤ ∑ _V₀ ∈ G_fin, (1 / 8 : ℝ) := by
          refine Finset.sum_le_sum (fun V₀ hV₀ => ?_)
          have h := (Set.Finite.mem_toFinset _).mp hV₀
          exact hgood_cond V₀ h.1 h.2
      _ = (G_fin.card : ℝ) * (1 / 8 : ℝ) := by simp
      _ ≤ (1 / 8 : ℝ) * (Nat.choose n n₀ : ℝ) := by linarith
  have hsum_total : ∑ V₀ ∈ P_n0, cond V₀ ≤ (1 / 4 : ℝ) * (Nat.choose n n₀ : ℝ) := by
    rw [← Finset.sum_sdiff hG_sub]
    linarith
  rw [Osi.Prelim.uniformSubsetProb_two_stage hr hn₀ E]
  have hmul := mul_le_mul_of_nonneg_left hsum_total (inv_nonneg.mpr hchoose_n0_pos.le)
  have hcancel : ((Nat.choose n n₀ : ℝ)⁻¹) * ((1 / 4 : ℝ) * (Nat.choose n n₀ : ℝ)) = 1 / 4 := by
    field_simp
  exact le_trans hmul (le_of_eq hcancel)

private lemma not_isOSIWithProb_of_lt_rank {n r k : ℕ} {α p_osi : ℝ}
    (hrn : r ≤ n) (hkr : k < r) (hα : 0 < α) (hp : 0 < p_osi)
    (Ω_prob : Type) [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob)
    (M : Ω_prob → Matrix (Fin n) (Fin k) ℝ) :
    ¬ IsOSIWithProb P M r α p_osi := by
  intro hOSI
  have hne : ((Finset.univ : Finset (Fin n)).powersetCard r).Nonempty := by
    rw [← Finset.card_pos, Finset.card_powersetCard]
    simpa using Nat.choose_pos hrn
  obtain ⟨R, hR_mem⟩ := hne
  have hR : R.card = r := (Finset.mem_powersetCard.mp hR_mem).2
  let Q : Matrix (Fin n) (Fin r) ℝ := coordFrame R hR
  have hprob := hOSI Q (Osi.Prelim.coordFrame_isIsometry R hR)
  have hemp : {ω : Ω_prob | MinEigenvalueAtLeast ((M ω).transpose * Q) α} = ∅ := by
    ext ω
    simp only [Set.mem_empty_iff_false, iff_false]
    change ¬ MinEigenvalueAtLeast ((M ω).transpose * Q) α
    let A : Matrix (Fin k) (Fin r) ℝ := (M ω).transpose * Q
    let f : (Fin r → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
      { toFun := A.mulVec
        map_add' := Matrix.mulVec_add A
        map_smul' := fun c v => by simp [Matrix.mulVec_smul] }
    have hfinrank : Module.finrank ℝ (Fin k → ℝ) < Module.finrank ℝ (Fin r → ℝ) := by
      simpa using hkr
    have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hfinrank
    obtain ⟨x, hx_ker, hx_ne⟩ := (LinearMap.ker f).ne_bot_iff.mp hker
    have hAx : A.mulVec x = 0 := LinearMap.mem_ker.mp hx_ker
    have hx_pos : 0 < vecSqNorm x := by
      have hex : ∃ j : Fin r, x j ≠ 0 := by
        by_contra hall
        exact hx_ne (funext fun j => Classical.not_not.mp fun hj => hall ⟨j, hj⟩)
      obtain ⟨j, hj⟩ := hex
      have hj_sq : 0 < (x j) ^ 2 := sq_pos_of_ne_zero hj
      have hj_le : (x j) ^ 2 ≤ vecSqNorm x :=
        Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ j)
      exact lt_of_lt_of_le hj_sq hj_le
    have hAx_sq : vecSqNorm (A.mulVec x) = 0 := by simp [vecSqNorm, hAx]
    refine Osi.Prelim.not_minEigenvalueAtLeast_of_witness A α x hx_pos ?_
    rw [hAx_sq]
    exact mul_pos hα hx_pos
  rw [hemp, MeasureTheory.measure_empty, ENNReal.toReal_zero] at hprob
  linarith

private lemma master_finite_scale (K α : ℝ) (hK : 1 ≤ K) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (c C_H C_n : ℝ) (r₀ : ℕ), 0 < c ∧ 0 < C_H ∧ 0 < C_n ∧ 3 ≤ r₀ ∧
      (∀ (n r k ζ : ℕ) (S : Matrix (Fin n) (Fin k) ℝ),
        r₀ ≤ r → r ≤ n →
        C_n * (r : ℝ) * (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 ≤ (n : ℝ) →
        r ≤ k → (k : ℝ) ≤ K * (r : ℝ) →
        (ζ : ℝ) ≤ c * Real.sqrt (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) →
        (∀ i : Fin n, (rowSupport S i).card ≤ ζ) →
        frobSq S ≤ 10 * (n : ℝ) →
        SatisfiesOverlapCond S ((C_H * (ζ : ℝ) ^ 6)⁻¹) →
        uniformSubsetProb n r
          (fun R => ∀ hR : R.card = r, MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α) ≤
          1 / 4) ∧
      (∀ (n r k ζ : ℕ), r₀ ≤ r → r ≤ n →
        C_n * (r : ℝ) * (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 ≤ (n : ℝ) →
        (k : ℝ) ≤ K * (r : ℝ) →
        ∀ (Ω_prob : Type) [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob),
          MeasureTheory.IsProbabilityMeasure P →
          ∀ M : Ω_prob → Matrix (Fin n) (Fin k) ℝ,
            IsRandomMatrix M →
            IsIsotropic P M →
            IsRowSparse P M ζ →
            SatisfiesOverlapWhp P M ((C_H * (ζ : ℝ) ^ 6)⁻¹) (9 / 10) →
            IsOSIWithProb P M r α (1 / 2) →
            c * Real.sqrt (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ≤ (ζ : ℝ)) := by
  obtain ⟨C₀, -, h82⟩ := lemma_8_2_SmallOrOneSparseElim
  obtain ⟨C_samp₀, -, h83⟩ := lemma_8_3_C4FreeSubgraph
  obtain ⟨C_samp₂, c_T, -, hc_T_pos, h97⟩ := theorem_9_7_WitnessForest
  let C_samp : ℝ := max C_samp₀ (max (C_samp₂ * K ^ 2) 1024)
  have hCsamp_ge0 : C_samp₀ ≤ C_samp := le_max_left _ _
  have hCsamp_ge2 : C_samp₂ * K ^ 2 ≤ C_samp :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hCsamp_1024 : 1024 ≤ C_samp :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hCsamp_pos : 0 < C_samp := lt_of_lt_of_le (by norm_num) hCsamp_1024
  let c : ℝ := α / 6000
  let C_H : ℝ := 512 * C_samp / α
  let C_n : ℝ := max (64 * K) (C_samp / α + 1)
  let M_log : ℝ :=
    max (Real.exp 1) (max (4 * (642 / α)) (max (2 * (C_samp / α + 1)) (368640 / c_T)))
  let r₀ : ℕ := max 3 (max (Nat.ceil (C₀ * K)) (Nat.ceil (Real.exp M_log)))
  have hc_pos : 0 < c := by positivity
  have hCH_pos : 0 < C_H := by positivity
  have hCn_pos : 0 < C_n := lt_of_lt_of_le (by positivity) (le_max_left (64 * K) _)
  have hr0_ge3 : 3 ≤ r₀ := le_max_left _ _
  have hpartA : ∀ (n r k ζ : ℕ) (S : Matrix (Fin n) (Fin k) ℝ),
      r₀ ≤ r → r ≤ n →
      C_n * (r : ℝ) * (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 ≤ (n : ℝ) →
      r ≤ k → (k : ℝ) ≤ K * (r : ℝ) →
      (ζ : ℝ) ≤ c * Real.sqrt (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) →
      (∀ i : Fin n, (rowSupport S i).card ≤ ζ) →
      frobSq S ≤ 10 * (n : ℝ) →
      SatisfiesOverlapCond S ((C_H * (ζ : ℝ) ^ 6)⁻¹) →
      uniformSubsetProb n r
        (fun R => ∀ hR : R.card = r, MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α) ≤
        1 / 4 := by
    intro n r k ζ S hr0 hrn hn hrk hk hζ_le hsparse hfrob hov
    have hr3 : 3 ≤ r := le_trans hr0_ge3 hr0
    have hC0K_le_r : C₀ * K ≤ (r : ℝ) := by
      have hceil_le : Nat.ceil (C₀ * K) ≤ r :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hr0)
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hceil_le)
    have hr_exp : Real.exp M_log ≤ (r : ℝ) := by
      have hceil_le : Nat.ceil (Real.exp M_log) ≤ r :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hr0)
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hceil_le)
    obtain ⟨_, _, _, hL1, _⟩ := log_bounds_of_exp_le (le_max_left _ _) hr_exp
    have h64Kr_le_n : 64 * K * (r : ℝ) ≤ (n : ℝ) := by
      have h64_Cn : 64 * K ≤ C_n := le_max_left _ _
      have hL3 : 1 ≤ (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 := one_le_pow₀ hL1
      have h1 : 64 * K * (r : ℝ) ≤ C_n * (r : ℝ) :=
        mul_le_mul_of_nonneg_right h64_Cn (Nat.cast_nonneg r)
      have h2 : C_n * (r : ℝ) ≤ C_n * (r : ℝ) *
          (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 := by
        simpa using mul_le_mul_of_nonneg_left hL3 (by positivity : 0 ≤ C_n * (r : ℝ))
      exact le_trans h1 (le_trans h2 hn)
    rcases eq_or_ne ζ 0 with rfl | hζ_ne0
    · exact zero_sparsity_capture hr3 hα0 hsparse
    rcases eq_or_ne ζ 1 with rfl | hζ_ne1
    · have helim := one_sparsity_small_or_one (show 1 ≤ n by omega) hα0 hsparse
      exact prob_le_quarter_of_small_or_one hrn
        (h82 K α n r k S hK hα0 hC0K_le_r h64Kr_le_n hk hrn helim)
    · have hζ2 : 2 ≤ ζ := by omega
      by_cases helim :
          (n : ℝ) / 16 ≤ (smallRows S α).card ∨ (n : ℝ) / 16 ≤ (oneSparseRows S).card
      · exact prob_le_quarter_of_small_or_one hrn
          (h82 K α n r k S hK hα0 hC0K_le_r h64Kr_le_n hk hrn helim)
      · have hclean := cleanRows_card_ge_of_not_elim hfrob helim
        let n₀ : ℕ := Nat.ceil (C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α)
        have hc1 : c ≤ 1 := by
          change α / 6000 ≤ 1
          linarith
        obtain ⟨hr_le_n0, hn0_le_n, -⟩ := samp_size_bounds hα0 hα1 hCsamp_1024
          (le_max_right _ _) hr3 hζ2 hL1 hc_pos hc1 hζ_le hn rfl
        let GoodV0 : Finset (Fin n) → Prop := fun V₀ =>
          let V_G0 := prunedRows S α 160 V₀
          (((V₀ \ cleanRows S α 160).card : ℝ) ≤ (n₀ : ℝ) / 4) ∧
            (((subCollidingPairs S V₀).card : ℝ) ≤ (n₀ : ℝ) / 16) ∧
            ((5 / 8 : ℝ) * (n₀ : ℝ) ≤ (V_G0.card : ℝ)) ∧
            IsC4FreeRows S V_G0 ∧
            ∀ i ∈ V_G0, α ≤ vecSqNorm (S i) ∧ vecSqNorm (S i) ≤ 160 ∧
              2 ≤ (rowSupport S i).card ∧ (rowSupport S i).card ≤ ζ
        have hgood_prob : (7 / 8 : ℝ) ≤ uniformSubsetProb n n₀ GoodV0 :=
          h83 C_samp α n k r ζ S hCsamp_ge0 hα0 hα1.le (by omega) hrk (by omega)
            hsparse hov hclean n₀ rfl hn0_le_n
        let E : Finset (Fin n) → Prop :=
          fun R => ∀ hR : R.card = r, MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α
        refine two_stage_good_bad_combine hr_le_n0 hn0_le_n GoodV0 E hgood_prob ?_
        intro V₀ hV0_card hV0_good
        let V_G0 : Finset (Fin n) := prunedRows S α 160 V₀
        have hVG0_sub : V_G0 ⊆ V₀ := by
          intro v hv
          have hm := (Set.Finite.mem_toFinset _).mp hv
          exact (Finset.mem_inter.mp hm.1).1
        have hVG0_card_le : V_G0.card ≤ n₀ :=
          le_trans (Finset.card_le_card hVG0_sub) (le_of_eq hV0_card)
        obtain ⟨-, -, hVG0_58, hVG0_c4, hVG0_rows⟩ := hV0_good
        obtain ⟨T, V_tree, x_tree, hT1, hT_ge, hVtree_sub, hVtree_disj, hxtree⟩ :=
          h97 K C_samp α n k r ζ n₀ S V_G0 hK hCsamp_ge2 hα0 hα1.le (by omega) hrk hk hζ2
            rfl hVG0_58 hVG0_card_le hVG0_c4 hVG0_rows
        let q : ℕ := Nat.ceil (640 * (ζ : ℝ) / α)
        let B : ℕ := 1 + ζ * q
        obtain ⟨h2B_le_r, hrate8⟩ := tree_size_and_rate_bounds hα0 hα1 hc_T_pos hCsamp_1024
          hr3 hζ2 hr_exp hζ_le rfl hT_ge
        have hsub_avoid :
            (Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ E R}).toFinset ⊆
              (Set.toFinite {R : Finset (Fin n) |
                R ⊆ V₀ ∧ R.card = r ∧ ∀ s : Fin T, ¬ V_tree s ⊆ R}).toFinset := by
          intro R hR_mem
          obtain ⟨hR_V0, hR_card, hER⟩ := (Set.Finite.mem_toFinset _).mp hR_mem
          refine (Set.Finite.mem_toFinset _).mpr ⟨hR_V0, hR_card, fun s hs_sub => ?_⟩
          obtain ⟨hx_supp, hx_norm, hx_St⟩ := hxtree s
          have hsupp_R : ∀ i : Fin n, i ∉ R → x_tree s i = 0 :=
            fun i hi => hx_supp i (fun hi_tree => hi (hs_sub hi_tree))
          have hy_pos : 0 < vecSqNorm (x_tree s) := lt_of_lt_of_le zero_lt_one hx_norm
          have hlt_St : vecSqNorm (S.transpose.mulVec (x_tree s)) < α * vecSqNorm (x_tree s) := by
            have : α / 4 < α * 1 := by linarith
            have : α * 1 ≤ α * vecSqNorm (x_tree s) :=
              mul_le_mul_of_nonneg_left hx_norm hα0.le
            linarith
          exact Osi.Prelim.not_minEigenvalueAtLeast_coordFrame_of_supported_witness
            S R hR_card α (x_tree s) hsupp_R hy_pos hlt_St (hER hR_card)
        have hcard_le :
            (((Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ E R}).toFinset).card : ℝ) ≤
              (((Set.toFinite {R : Finset (Fin n) |
                R ⊆ V₀ ∧ R.card = r ∧ ∀ s : Fin T, ¬ V_tree s ⊆ R}).toFinset).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub_avoid
        have hdiv_le :
            (((Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ E R}).toFinset).card : ℝ) /
                (Nat.choose n₀ r : ℝ) ≤
              (((Set.toFinite {R : Finset (Fin n) |
                R ⊆ V₀ ∧ R.card = r ∧ ∀ s : Fin T, ¬ V_tree s ⊆ R}).toFinset).card : ℝ) /
                (Nat.choose n₀ r : ℝ) :=
          div_le_div_of_nonneg_right hcard_le (Nat.cast_nonneg _)
        have hcheb := Osi.Prelim.disjoint_subsets_capture_chebyshev V₀ hV0_card hr_le_n0
          (show 1 ≤ B by omega) h2B_le_r hT1 V_tree
          (fun s => ⟨ Finset.Subset.trans (hVtree_sub s).1 hVG0_sub, (hVtree_sub s).2 ⟩)
          hVtree_disj
        have hinv_eighth : 1 / ((T : ℝ) * ((r : ℝ) / (2 * (n₀ : ℝ))) ^ B) ≤ 1 / 8 :=
          one_div_le_one_div_of_le (by norm_num) hrate8
        exact le_trans hdiv_le (le_trans hcheb hinv_eighth)
  have hpartB : ∀ (n r k ζ : ℕ), r₀ ≤ r → r ≤ n →
      C_n * (r : ℝ) * (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 ≤ (n : ℝ) →
      (k : ℝ) ≤ K * (r : ℝ) →
      ∀ (Ω_prob : Type) [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob),
        MeasureTheory.IsProbabilityMeasure P →
        ∀ M : Ω_prob → Matrix (Fin n) (Fin k) ℝ,
          IsRandomMatrix M →
          IsIsotropic P M →
          IsRowSparse P M ζ →
          SatisfiesOverlapWhp P M ((C_H * (ζ : ℝ) ^ 6)⁻¹) (9 / 10) →
          IsOSIWithProb P M r α (1 / 2) →
          c * Real.sqrt (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ≤ (ζ : ℝ) := by
    intro n r k ζ hr0 hrn hn hk Ω_prob _ P hP M hM hIso hSparse hOv hOSI
    have hr3 : 3 ≤ r := le_trans hr0_ge3 hr0
    by_cases hrk : r ≤ k
    · by_contra hlt
      have hle : (ζ : ℝ) ≤ c * Real.sqrt (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) :=
        le_of_not_ge hlt
      have hη : 0 ≤ (C_H * (ζ : ℝ) ^ 6)⁻¹ := inv_nonneg.mpr (by positivity)
      have hnot := lemma_10_1_CoordinateSubspaceReduction n r k ζ α ((C_H * (ζ : ℝ) ^ 6)⁻¹)
        (1 / 2) (by omega) hrn hα0 hα1 hη (by norm_num)
        (fun S hS_sp hS_frob hS_ov => hpartA n r k ζ S hr0 hrn hn hrk hk hle hS_sp hS_frob hS_ov)
        Ω_prob P hP M hM hIso hSparse hOv
      exact hnot hOSI
    · exfalso
      exact not_isOSIWithProb_of_lt_rank hrn (by omega) hα0 (by norm_num)
        Ω_prob P M hOSI
  exact ⟨c, C_H, C_n, r₀, hc_pos, hCH_pos, hCn_pos, hr0_ge3, hpartA, hpartB⟩

/-- **Theorem 10.2 (Finite-scale coordinate-capture theorem & full OSI lower bound, p. 46).** -/
theorem theorem_10_2_FiniteScale : Theorem_10_2_FiniteScale := by
  intro K α hK hα0 hα1
  obtain ⟨c, C_H, C_n, r₀, hc, hCH, hCn, hr0, hpartA, hpartB⟩ :=
    master_finite_scale K α hK hα0 hα1
  refine ⟨c, C_H, C_n, r₀, hc, hCH, hCn, hr0, hpartA, ?_⟩
  intro n r k ζ hr0_le hrn hn hk Ω_prob _ P hP M hM hIso hSparse hOv hOSI
  refine hpartB n r k ζ hr0_le hrn hn hk Ω_prob P hP M hM hIso hSparse hOv ?_
  intro Q hQ
  linarith [hOSI Q hQ]

/-- **Theorem 1.3 (`1/2`-probability OSI lower bound, p. 4 & p. 46).** -/
theorem theorem_1_3_LowerBound_HalfProb : Theorem_1_3_LowerBound_HalfProb := by
  intro K α hK hα0 hα1
  obtain ⟨c, C_H, C_n, r₀, hc, hCH, hCn, hr0, -, hpartB⟩ :=
    master_finite_scale K α hK hα0 hα1
  exact ⟨c, C_H, C_n, r₀, hc, hCH, hCn, hr0, hpartB⟩

/-- **Theorem 1.3 (`19/20`-OSI lower bound, p. 4).** -/
theorem theorem_1_3_LowerBound : Theorem_1_3_LowerBound := by
  intro K α hK hα0 hα1
  obtain ⟨c, C_H, C_n, r₀, hc, hCH, hCn, hr0, hhalf⟩ :=
    theorem_1_3_LowerBound_HalfProb K α hK hα0 hα1
  refine ⟨c, C_H, C_n, r₀, hc, hCH, hCn, hr0, ?_⟩
  intro n r k ζ hr0_le hrn hn hk Ω_prob _ P hP M hM hIso hSparse hOv hOSI
  refine hhalf n r k ζ hr0_le hrn hn hk Ω_prob P hP M hM hIso hSparse hOv ?_
  intro Q hQ
  linarith [hOSI Q hQ]

/-- **Theorem 1.3 (Quadratic ambient dimension `n ≥ 100 r²`, p. 4).** -/
theorem theorem_1_3_QuadraticN : Theorem_1_3_QuadraticN := by
  intro K α hK hα0 hα1
  obtain ⟨c, C_H, C_n, r₀', hc, hCH, hCn, hr0', h13⟩ :=
    theorem_1_3_LowerBound K α hK hα0 hα1
  let M_quad : ℝ := max (Real.exp 1) (24 * C_n / 100)
  let r₀ : ℕ := max r₀' (Nat.ceil (Real.exp M_quad))
  have hr0_ge3 : 3 ≤ r₀ := le_trans hr0' (le_max_left _ _)
  refine ⟨c, C_H, r₀, hc, hCH, hr0_ge3, ?_⟩
  intro n r k ζ hr0_le hn_quad hk Ω_prob _ P hP M hM hIso hSparse hOv hOSI
  have hr0'_le : r₀' ≤ r := le_trans (le_max_left _ _) hr0_le
  have hr3 : 3 ≤ r := le_trans hr0_ge3 hr0_le
  have hrn : r ≤ n := by nlinarith
  have hr_exp : Real.exp M_quad ≤ (r : ℝ) := by
    have hceil_le : Nat.ceil (Real.exp M_quad) ≤ r :=
      le_trans (le_max_right _ _) hr0_le
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast hceil_le)
  obtain ⟨hMt, ht1, _, hL1, hLt⟩ := log_bounds_of_exp_le (le_max_left _ _) hr_exp
  have ht_Cn : 24 * C_n / 100 ≤ Real.log (r : ℝ) := le_trans (le_max_right _ _) hMt
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hexp4 := Real.pow_div_factorial_le_exp (Real.log (r : ℝ))
    (le_of_lt (lt_trans zero_lt_one ht1)) 4
  rw [Real.exp_log hr_pos] at hexp4
  have ht4_le : (Real.log (r : ℝ)) ^ 4 ≤ 24 * (r : ℝ) := by
    norm_num [Nat.factorial] at hexp4
    linarith
  have hL3_le : (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 ≤ (Real.log (r : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (le_trans zero_le_one hL1) hLt 3
  have hCn_t3 : C_n * (Real.log (r : ℝ)) ^ 3 ≤ 100 * (r : ℝ) := by
    have ht3_nonneg : 0 ≤ (Real.log (r : ℝ)) ^ 3 := by positivity
    have h1 : (24 * C_n / 100) * (Real.log (r : ℝ)) ^ 3 ≤ (Real.log (r : ℝ)) ^ 4 := by
      calc (24 * C_n / 100) * (Real.log (r : ℝ)) ^ 3
          ≤ Real.log (r : ℝ) * (Real.log (r : ℝ)) ^ 3 :=
            mul_le_mul_of_nonneg_right ht_Cn ht3_nonneg
        _ = (Real.log (r : ℝ)) ^ 4 := by ring
    linarith
  have hn_log : C_n * (r : ℝ) * (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 ≤ (n : ℝ) := by
    have hn_quad_real : 100 * (r : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn_quad
    have h1 : C_n * (r : ℝ) * (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 ≤
        C_n * (r : ℝ) * (Real.log (r : ℝ)) ^ 3 :=
      mul_le_mul_of_nonneg_left hL3_le (by positivity)
    have h2 : C_n * (r : ℝ) * (Real.log (r : ℝ)) ^ 3 ≤ 100 * (r : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hCn_t3 hr_pos.le
      linarith
    exact le_trans h1 (le_trans h2 hn_quad_real)
  exact h13 n r k ζ hr0'_le hrn hn_log hk Ω_prob P hP M hM hIso hSparse hOv hOSI

end Osi.LowerBound

