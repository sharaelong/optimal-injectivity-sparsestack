import Osi.Spec
import Osi.Prelim.SubspaceSing
import Osi.UpperBound.OverlapProp
import Osi.LowerBound.Endgame
import SparseStack.Main
import SparseStack.CaseA
import SparseStack.CaseB

/-!
# Section 7 & Section 1.1: General-Parameter Theorem 1.1 and Optimal Tightness

Proves `Theorem_1_1_Schedule`, `Theorem_1_1_GeneralParams`, `Theorem_1_1_PaperRange`, and
`Theorem_Optimal_SparseStack_Tightness`.
-/

namespace Osi.UpperBound

namespace GenSparseStack

open SparseStack SparseFock

private lemma zeta_ge_32768 {r ζ : ℕ} (hr : 2 ≤ r)
    (hζ : (constC : ℝ) * Real.sqrt (logER r) ≤ (ζ : ℝ)) :
    32768 ≤ ζ := by
  have h1 : 1 ≤ logER r := one_le_logER (by omega)
  have hs : 1 ≤ Real.sqrt (logER r) := Real.one_le_sqrt.mpr h1
  have hC : (constC : ℝ) = 32768 := constC_real
  rw [hC] at hζ
  have hR : (32768 : ℝ) ≤ (ζ : ℝ) := by nlinarith
  exact_mod_cast hR

private lemma sketch_ratio_le_gen {r ζ b : ℕ} (hr : 2 ≤ r)
    (hζb : constK * r ≤ ζ * b) :
    ((r : ℝ) + 2 * (CaseA.momentOrder r : ℝ) + 1) / ((b : ℝ) * (ζ : ℝ)) ≤
      5 / (constK : ℝ) := by
  have h1 := CaseA.two_momentOrder_add_one_le (r := r) (by omega)
  have h2 := logER_le (r := r) (by omega)
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hnum : (r : ℝ) + 2 * (CaseA.momentOrder r : ℝ) + 1 ≤ 5 * r := by linarith
  have hK : (constK : ℝ) * r ≤ (b : ℝ) * (ζ : ℝ) := by
    have hbζ : constK * r ≤ b * ζ := by rw [Nat.mul_comm b ζ]; exact hζb
    exact_mod_cast hbζ
  have hKpos : (0 : ℝ) < constK := by norm_num [constK]
  have hden : 0 < (b : ℝ) * (ζ : ℝ) :=
    lt_of_lt_of_le (mul_pos hKpos (by linarith)) hK
  rw [div_le_div_iff₀ hden hKpos]
  calc ((r : ℝ) + 2 * (CaseA.momentOrder r : ℝ) + 1) * constK
      ≤ 5 * r * constK := mul_le_mul_of_nonneg_right hnum hKpos.le
    _ = 5 * (constK * r) := by ring
    _ ≤ 5 * ((b : ℝ) * (ζ : ℝ)) := by linarith

private lemma block_ratio_le_gen {r ζ : ℕ} (hr : 2 ≤ r)
    (hζ : (constC : ℝ) * Real.sqrt (logER r) ≤ (ζ : ℝ))
    (hreg : logER r < 64 ∨ 104 * logER r ≤ (ζ : ℝ)) :
    (2 * (CaseA.momentOrder r : ℝ) + 1) / (ζ : ℝ) ≤ 69 / 6656 := by
  have h1 := CaseA.two_momentOrder_add_one_le (r := r) (by omega)
  have hζ32768 : (32768 : ℝ) ≤ (ζ : ℝ) := by exact_mod_cast zeta_ge_32768 hr hζ
  have hζpos : (0 : ℝ) < (ζ : ℝ) := by linarith
  rw [div_le_div_iff₀ hζpos (by norm_num)]
  by_cases hL : logER r < 64
  · linarith
  · have h104 : 104 * logER r ≤ (ζ : ℝ) := hreg.resolve_left hL
    have hL64 : 64 ≤ logER r := not_lt.mp hL
    linarith

section CaseAGen

open scoped Matrix.Norms.L2Operator

private lemma general_caseA {n r ζ b : ℕ} (hr : 2 ≤ r) (hb : 2 ≤ b)
    (hζ : (constC : ℝ) * Real.sqrt (logER r) ≤ (ζ : ℝ))
    (hζb : constK * r ≤ ζ * b)
    (Q : Matrix (Fin n) (Fin r) ℝ) (hQ : Q.transpose * Q = 1)
    (hreg : logER r < 64 ∨ 104 * logER r ≤ (ζ : ℝ)) :
    (19 / 20 : ℝ) ≤ uniformProb (SketchSample ζ b n)
      (fun ω => QuadraticLowerBound (sketchMatrix ω * Q) constAlpha) := by
  have hs1 : 1 ≤ ζ := le_trans (by norm_num) (zeta_ge_32768 hr hζ)
  have hb0 : 0 < b := by omega
  have hp1 : 1 ≤ CaseA.momentOrder r := CaseA.one_le_momentOrder (by omega)
  have hmom := stack_moment hs1 hb Q hQ (CaseA.momentOrder r) hp1
  have hS := CaseA.combined_le (sketch_ratio_le_gen hr hζb) (block_ratio_le_gen hr hζ hreg)
  have hS0 : 0 ≤ Real.sqrt (((r : ℝ) + 2 * (CaseA.momentOrder r : ℝ) + 1) /
        ((b : ℝ) * (ζ : ℝ))) +
      ((r : ℝ) + 2 * (CaseA.momentOrder r : ℝ) + 1) / ((b : ℝ) * (ζ : ℝ)) +
      (2 * (CaseA.momentOrder r : ℝ) + 1) / (ζ : ℝ) := by
    positivity
  have hα : constAlpha < 1 := by
    unfold constAlpha
    norm_num
  have hfail : (sketchLaw ζ b n hb0).prob
      {ω | QuadraticLowerBound (sketchMatrix ω * Q) constAlpha}ᶜ ≤
        (r : ℝ) * (4 / 11) ^ (2 * CaseA.momentOrder r) :=
    CaseA.failure_le (sketchLaw ζ b n hb0)
      (fun ω : SketchSample ζ b n => sketchMatrix ω * Q) (r : ℝ)
      (CaseA.momentOrder r) hα hS0 hS (Nat.cast_nonneg r) hmom
  have htail := CaseA.mul_four_elevenths_pow_le (r := r) (by omega)
  rw [uniformProb_eq_prob hb0]
  have hcompl := FiniteLaw.prob_compl (sketchLaw ζ b n hb0)
    {ω | QuadraticLowerBound (sketchMatrix ω * Q) constAlpha}
  linarith

end CaseAGen

private lemma general_caseB_params {r ζ b : ℕ} (hr : 2 ≤ r) (hL : 64 ≤ logER r)
    (hζ_lo : (constC : ℝ) * Real.sqrt (logER r) ≤ (ζ : ℝ))
    (hζ_hi : (ζ : ℝ) < 104 * logER r)
    (hζb : constK * r ≤ ζ * b) :
    11 ≤ r ∧ 1 ≤ ζ / 2 ∧ ζ / 2 ≤ r ∧
      locTheta * r ≤ b * (ζ / 2) ∧
      1 ≤ locWidth r (ζ / 2) ∧ 8 * locWidth r (ζ / 2) ≤ r ∧
      16 * (8 * locWidth r (ζ / 2)) ≤ b ∧
      cStarRep * Real.sqrt (Real.log (Real.exp 1 * r)) ≤ (ζ / 2 : ℕ) ∧
      ((ζ / 2 : ℕ) : ℝ) < 256 * Real.log (Real.exp 1 * r) ∧
      kStarRep * r ≤ b * (ζ / 2) ∧
      rho0 ≤ ((ζ / 2 : ℕ) : ℝ) / (ζ : ℝ) := by
  have hLdef : Real.log (Real.exp 1 * r) = logER r := rfl
  rw [hLdef]
  have hsqrt : (32768 : ℝ) * Real.sqrt (logER r) ≤ (ζ : ℝ) := by
    rwa [constC_real] at hζ_lo
  have hbζ : 160000000 * r ≤ b * ζ := by
    have hK : constK = 160000000 := rfl
    rw [Nat.mul_comm b ζ]
    rwa [hK] at hζb
  have hlocM : (locM : ℝ) = 440000 := by norm_num [locM]
  set L := logER r
  set q := ζ / 2
  set m := locWidth r q with hmset
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L
  have hs0 : 0 < s := Real.sqrt_pos.mpr hL0
  have hss : s * s = L := Real.mul_self_sqrt hL0.le
  have hs315 : 315 < s := by nlinarith
  have hLbig : 99225 ≤ L := by nlinarith
  have hζbigR : (10321920 : ℝ) ≤ ζ := by linarith
  have hrL : 300 * L ≤ r := r_ge_300_logER hr (by linarith)
  have hζbig : 10000000 ≤ ζ := by
    have : (10000000 : ℝ) ≤ ζ := by linarith
    exact_mod_cast this
  have hζr : ζ ≤ r := by
    have : (ζ : ℝ) ≤ r := by linarith
    exact_mod_cast this
  have hq1 : 499 * ζ ≤ 1000 * q := by omega
  have hq5 : 5000000 ≤ q := by omega
  have hqr : q ≤ r := by omega
  have h2q : 2 * q ≤ ζ := by omega
  have hbq : 79840000 * r ≤ b * q := by
    have h1 : b * (499 * ζ) ≤ b * (1000 * q) := Nat.mul_le_mul_left b hq1
    have h2 : 499 * (160000000 * r) ≤ 499 * (b * ζ) := Nat.mul_le_mul_left 499 hbζ
    have h3 : 1000 * (79840000 * r) ≤ 1000 * (b * q) := by
      calc 1000 * (79840000 * r) = 499 * (160000000 * r) := by ring
        _ ≤ 499 * (b * ζ) := h2
        _ = b * (499 * ζ) := by ring
        _ ≤ b * (1000 * q) := h1
        _ = 1000 * (b * q) := by ring
    omega
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hζ0 : (0 : ℝ) < ζ := by exact_mod_cast (show 0 < ζ by omega)
  have hq1R : (499 : ℝ) * ζ ≤ 1000 * q := by exact_mod_cast hq1
  have hq5R : (5000000 : ℝ) ≤ q := by exact_mod_cast hq5
  have h2qR : (2 : ℝ) * q ≤ ζ := by exact_mod_cast h2q
  have hbqR : (79840000 : ℝ) * r ≤ b * q := by exact_mod_cast hbq
  have hmdef : m = Nat.ceil ((440000 : ℝ) * r / q) := by
    simp only [hmset, locWidth, hlocM]
  have hm_lt : (m : ℝ) < 440000 * r / q + 1 := by
    rw [hmdef]
    exact Nat.ceil_lt_add_one (by positivity)
  have hmq : (m : ℝ) * q < 440000 * r + q := by
    have := mul_lt_mul_of_pos_right hm_lt hq0
    rwa [add_mul, div_mul_cancel₀ _ hq0.ne', one_mul] at this
  have hm1 : 1 ≤ m := by
    rw [hmdef]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have h8m : 8 * m ≤ r := by
    have hqr' : (5000000 : ℝ) * r ≤ q * r := mul_le_mul_of_nonneg_right hq5R hr0.le
    have e1 : (8 * m : ℝ) * q < r * q := by nlinarith
    have e2 : (8 * m : ℝ) < r := lt_of_mul_lt_mul_right e1 hq0.le
    have e3 : 8 * m < r := by exact_mod_cast e2
    omega
  have h128m : 16 * (8 * m) ≤ b := by
    have e1 : (128 * m : ℝ) * q < b * q := by nlinarith
    have e2 : (128 * m : ℝ) < b := lt_of_mul_lt_mul_right e1 hq0.le
    have e3 : 128 * m < b := by exact_mod_cast e2
    omega
  refine ⟨by omega, by omega, hqr, ?_, hm1, h8m, h128m, ?_, ?_, hbq, ?_⟩
  · show 48800 * r ≤ b * q
    omega
  · unfold cStarRep
    linarith
  · linarith
  · rw [le_div_iff₀ hζ0]
    unfold rho0
    linarith

private lemma sqNorm_nonneg_gen {ι : Type} [Fintype ι] (v : ι → ℝ) : 0 ≤ sqNorm v := by
  unfold sqNorm dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

private lemma general_caseB {n r ζ b : ℕ} (hr : 2 ≤ r) (hb : 2 ≤ b)
    (hζ_lo : (constC : ℝ) * Real.sqrt (logER r) ≤ (ζ : ℝ))
    (hζb : constK * r ≤ ζ * b)
    (Q : Matrix (Fin n) (Fin r) ℝ) (hQ : Q.transpose * Q = 1)
    (hL : 64 ≤ logER r) (hζ_hi : (ζ : ℝ) < 104 * logER r) :
    (19 / 20 : ℝ) ≤ uniformProb (SketchSample ζ b n)
      (fun ω => QuadraticLowerBound (sketchMatrix ω * Q) constAlpha) := by
  classical
  obtain ⟨hr11, hq1, hqr, hθ, hm1, hm8, hm16, hqC, hqreg, hbq, hρ⟩ :=
    general_caseB_params hr hL hζ_lo hζ_hi hζb
  have hb0 : 0 < b := by omega
  set q := ζ / 2
  set m := locWidth r q
  have h2q : q + q ≤ ζ := by omega
  let f₁ : Fin q → Fin ζ := fun t => ⟨t.1, by have := t.2; omega⟩
  let f₂ : Fin q → Fin ζ := fun t => ⟨q + t.1, by have := t.2; omega⟩
  have hf₁ : Function.Injective f₁ := by
    intro a c h
    have := congrArg Fin.val h
    exact Fin.ext this
  have hf₂ : Function.Injective f₂ := by
    intro a c h
    have := congrArg Fin.val h
    simp only [f₂] at this
    exact Fin.ext (by omega)
  have hdisj : ∀ t₁ t₂, f₁ t₁ ≠ f₂ t₂ := by
    intro t₁ t₂ h
    have := congrArg Fin.val h
    simp only [f₁, f₂] at this
    have := t₁.2
    omega
  let E₁ : SketchSample q b n → Prop := fun ω₁ =>
    ∀ x : Fin r → ℝ, sqNorm x = 1 → 1 / 9 ≤ distSparseSq m (Q.mulVec x) →
      lambdaSq ≤ sqNorm ((sketchMatrix ω₁ * Q).mulVec x)
  have hE₁ : 1 - 3 / 20000 ≤ (sketchLaw q b n hb0).prob {ω₁ | E₁ ω₁} := by
    have hloc := localization hr11 hq1 hqr hb0 hθ Q hQ
    apply one_sub_le_prob_of_prob_compl_le
    refine le_trans (FiniteLaw.prob_mono _ ?_) hloc
    intro ω₁ hω₁
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, E₁] at hω₁ ⊢
    push Not at hω₁
    exact hω₁
  have hcertE : ∀ ω₁, E₁ ω₁ → ∃ I : Finset (Fin n), I.card ≤ 8 * m ∧
      ∀ x, ∑ i ∈ Iᶜ, (Q.mulVec x i) ^ 2 ≤
        uCert * sqNorm x + vCert * sqNorm ((sketchMatrix ω₁ * Q).mulVec x) :=
    fun ω₁ h => certificate hm1 Q hQ (sketchMatrix ω₁ * Q) h
  let Isel : SketchSample q b n → Finset (Fin n) := fun ω₁ =>
    if h : E₁ ω₁ then Classical.choose (hcertE ω₁ h) else ∅
  have hIsel : ∀ ω₁ (h : E₁ ω₁), (Isel ω₁).card ≤ 8 * m ∧
      ∀ x, ∑ i ∈ (Isel ω₁)ᶜ, (Q.mulVec x i) ^ 2 ≤
        uCert * sqNorm x + vCert * sqNorm ((sketchMatrix ω₁ * Q).mulVec x) := by
    intro ω₁ h
    have hI : Isel ω₁ = Classical.choose (hcertE ω₁ h) := dif_pos h
    rw [hI]
    exact Classical.choose_spec (hcertE ω₁ h)
  have hbas := fun I : Finset (Fin n) => background_basis Q I
  choose dsel Vsel Bsel hBsel using hbas
  let E₂ : SketchSample q b n → SketchSample q b n → Prop := fun ω₁ ω₂ =>
    ∀ h : Fin n → ℝ, (∀ i, i ∉ Isel ω₁ → h i = 0) → ∀ f : Fin (dsel (Isel ω₁)) → ℝ,
      betaRep * sqNorm h ≤
        sqNorm ((sketchMatrix ω₂).mulVec (h + (Vsel (Isel ω₁)).mulVec f)) + t0 * sqNorm f
  have hE₂ : ∀ ω₁, E₁ ω₁ → 1 - 997 / 20000 ≤ (sketchLaw q b n hb0).prob {ω₂ | E₂ ω₁ ω₂} := by
    intro ω₁ h₁
    obtain ⟨hcard, -⟩ := hIsel ω₁ h₁
    obtain ⟨hd, hV, hVs, -⟩ := hBsel (Isel ω₁)
    exact head_repair hr hb0 hqC hqreg hbq (Isel ω₁) (by omega) (by omega) (Vsel (Isel ω₁)) hV
      hVs hd
  have h2 := two_stage_independence hb0 f₁ f₂ hf₁ hf₂ hdisj E₁ E₂
    (by norm_num : (0 : ℝ) ≤ 997 / 20000) hE₁ hE₂
  rw [uniformProb_eq_prob hb0]
  refine le_trans (by norm_num : (19 / 20 : ℝ) ≤ 1 - 3 / 20000 - 997 / 20000)
    (le_trans h2 (FiniteLaw.prob_mono _ ?_))
  rintro ω ⟨h₁, h₂⟩
  obtain ⟨-, hcert⟩ := hIsel (blockRestrict f₁ ω) h₁
  obtain ⟨-, hV, -, hBJ⟩ := hBsel (Isel (blockRestrict f₁ ω))
  have key := caseB_combine Q hQ (Isel (blockRestrict f₁ ω)) (Vsel (Isel (blockRestrict f₁ ω))) hV
    (Bsel (Isel (blockRestrict f₁ ω))) hBJ
    (fun v => sqNorm ((sketchMatrix (blockRestrict f₁ ω)).mulVec v))
    (fun v => sqNorm ((sketchMatrix (blockRestrict f₂ ω)).mulVec v))
    (fun v => sqNorm ((sketchMatrix ω).mulVec v)) ((q : ℝ) / ζ) hρ
    (fun v => sqNorm_sketch_ge_groups f₁ f₂ hf₁ hf₂ hdisj ω v)
    (fun x => by
      have := hcert x
      rwa [← Matrix.mulVec_mulVec] at this)
    h₂ (fun _ => sqNorm_nonneg_gen _) (fun _ => sqNorm_nonneg_gen _)
  show QuadraticLowerBound (sketchMatrix ω * Q) constAlpha
  intro x
  have hx := key x
  rw [← Matrix.mulVec_mulVec]
  exact hx

theorem general_constantInjection {n r ζ b : ℕ}
    (hr : 2 ≤ r) (hb : 2 ≤ b)
    (hζ : (constC : ℝ) * Real.sqrt (logER r) ≤ (ζ : ℝ))
    (hζb : constK * r ≤ ζ * b)
    (Q : Matrix (Fin n) (Fin r) ℝ) (hQ : Q.transpose * Q = 1) :
    (19 / 20 : ℝ) ≤ uniformProb (SketchSample ζ b n)
      (fun ω => MinEigenvalueAtLeast (sketchMatrix ω * Q) constAlpha) := by
  have hev : (fun ω : SketchSample ζ b n =>
      MinEigenvalueAtLeast (sketchMatrix ω * Q) constAlpha) =
    (fun ω => QuadraticLowerBound (sketchMatrix ω * Q) constAlpha) := by
    funext ω
    exact propext (minEigenvalueAtLeast_iff_quadraticLowerBound _ _)
  rw [hev]
  by_cases hL : logER r < 64
  · exact general_caseA hr hb hζ hζb Q hQ (Or.inl hL)
  · by_cases h104 : 104 * logER r ≤ (ζ : ℝ)
    · exact general_caseA hr hb hζ hζb Q hQ (Or.inr h104)
    · exact general_caseB hr hb hζ hζb Q hQ (not_lt.mp hL) (not_le.mp h104)

end GenSparseStack

open Osi.Spec

private lemma constAlpha_gt : (1 / 10000 : ℝ) < constAlpha := by
  unfold constAlpha
  norm_num

private lemma constAlpha_lt_one : constAlpha < 1 := by
  unfold constAlpha
  norm_num

private lemma constAlpha_pos : (0 : ℝ) < constAlpha := by
  unfold constAlpha
  norm_num

private lemma numBlocks_le_two_constC_mul_sqrt {r : ℕ} (hr : 2 ≤ r) :
    (numBlocks r : ℝ) ≤ 2 * (constC : ℝ) * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))) := by
  have h1 : 1 ≤ SparseStack.logER r := SparseStack.one_le_logER (by omega)
  have hs : 1 ≤ Real.sqrt (SparseStack.logER r) := Real.one_le_sqrt.mpr h1
  have hlt : (SparseStack.numBlocks r : ℝ) <
      (SparseStack.constC : ℝ) * Real.sqrt (SparseStack.logER r) + 1 :=
    SparseStack.numBlocks_lt hr
  have hC : (SparseStack.constC : ℝ) = 32768 := SparseStack.constC_real
  change (SparseStack.numBlocks r : ℝ) ≤
    2 * (SparseStack.constC : ℝ) * Real.sqrt (SparseStack.logER r)
  nlinarith

private lemma logER_pow_ten_le {r : ℕ} (hr : 2 ≤ r) :
    (SparseStack.logER r) ^ 10 ≤ 3 * (10 : ℝ) ^ 10 * (r : ℝ) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have her_pos : 0 < Real.exp 1 * (r : ℝ) := mul_pos (Real.exp_pos 1) hr_pos
  have hL1 : 1 ≤ SparseStack.logER r := SparseStack.one_le_logER (by omega)
  have hL0 : 0 ≤ SparseStack.logER r / 10 := by linarith
  have hexp_le : SparseStack.logER r / 10 ≤ Real.exp (SparseStack.logER r / 10) := by
    have h := Real.add_one_le_exp (SparseStack.logER r / 10)
    linarith
  have hpow : (SparseStack.logER r / 10) ^ 10 ≤ (Real.exp (SparseStack.logER r / 10)) ^ 10 :=
    pow_le_pow_left₀ hL0 hexp_le 10
  have hexp10 : (Real.exp (SparseStack.logER r / 10)) ^ 10 = Real.exp 1 * (r : ℝ) := by
    rw [← Real.exp_nat_mul]
    have hmul : (10 : ℕ) * (SparseStack.logER r / 10) = SparseStack.logER r := by
      push_cast
      ring
    rw [hmul]
    exact Real.exp_log her_pos
  have he3 : Real.exp 1 * (r : ℝ) ≤ 3 * (r : ℝ) := by
    have he : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
    exact mul_le_mul_of_nonneg_right he hr_pos.le
  have hdiv : (SparseStack.logER r) ^ 10 / (10 : ℝ) ^ 10 ≤ 3 * (r : ℝ) := by
    rw [← div_pow]
    linarith
  rw [div_le_iff₀ (by positivity)] at hdiv
  linarith

private lemma overlap_param_le_of_large_r {C_H : ℝ} (hCH : 0 < C_H) {r : ℕ} (hr : 2 ≤ r)
    (hr_big :
      Nat.ceil (3 * (10 : ℝ) ^ 10 *
        (5 * C_H * (2 * (constC : ℝ)) ^ 10 / (2 * (constK : ℝ))) ^ 2) ≤ r) :
    5 * (numBlocks r : ℝ) ^ 4 / (2 * ((numBlocks r * numBuckets r : ℕ) : ℝ)) ≤
      (C_H * (numBlocks r : ℝ) ^ 6)⁻¹ := by
  set A : ℝ := 5 * C_H * (2 * (constC : ℝ)) ^ 10 / (2 * (constK : ℝ))
  set L : ℝ := SparseStack.logER r
  have hL1 : 1 ≤ L := SparseStack.one_le_logER (by omega)
  have hL0 : 0 ≤ L := by linarith
  have hCpos : (0 : ℝ) < (constC : ℝ) := by norm_num [constC]
  have hKpos : (0 : ℝ) < (constK : ℝ) := by norm_num [constK]
  have hA0 : 0 < A := by positivity
  have hrA : 3 * (10 : ℝ) ^ 10 * A ^ 2 ≤ (r : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hr_big)
  have hL10 : L ^ 10 ≤ 3 * (10 : ℝ) ^ 10 * (r : ℝ) := logER_pow_ten_le hr
  have hAL_sq : (A * L ^ 5) ^ 2 ≤ (r : ℝ) ^ 2 := by
    calc (A * L ^ 5) ^ 2 = A ^ 2 * L ^ 10 := by ring
      _ ≤ A ^ 2 * (3 * (10 : ℝ) ^ 10 * (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hL10 (sq_nonneg A)
      _ = (3 * (10 : ℝ) ^ 10 * A ^ 2) * (r : ℝ) := by ring
      _ ≤ (r : ℝ) * (r : ℝ) := mul_le_mul_of_nonneg_right hrA (Nat.cast_nonneg r)
      _ = (r : ℝ) ^ 2 := by ring
  have hAL : A * L ^ 5 ≤ (r : ℝ) := by
    have hAL0 : 0 ≤ A * L ^ 5 := by positivity
    have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    nlinarith
  have h5CH : 5 * C_H * (2 * (constC : ℝ)) ^ 10 * L ^ 5 ≤ 2 * (constK : ℝ) * (r : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hAL (show (0 : ℝ) ≤ 2 * (constK : ℝ) by positivity)
    have hK2 : (2 * (constK : ℝ)) ≠ 0 := by positivity
    have heq : (2 * (constK : ℝ)) * (A * L ^ 5) =
        5 * C_H * (2 * (constC : ℝ)) ^ 10 * L ^ 5 := by
      simp only [A]
      field_simp
    linarith
  have hζ_le : (numBlocks r : ℝ) ≤ 2 * (constC : ℝ) * Real.sqrt L :=
    numBlocks_le_two_constC_mul_sqrt hr
  have hζ10 : (numBlocks r : ℝ) ^ 10 ≤ (2 * (constC : ℝ)) ^ 10 * L ^ 5 := by
    calc (numBlocks r : ℝ) ^ 10
        ≤ (2 * (constC : ℝ) * Real.sqrt L) ^ 10 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hζ_le 10
      _ = (2 * (constC : ℝ)) ^ 10 * ((Real.sqrt L) ^ 2) ^ 5 := by ring
      _ = (2 * (constC : ℝ)) ^ 10 * L ^ 5 := by rw [Real.sq_sqrt hL0]
  have hkb_nat : constK * r ≤ numBlocks r * numBuckets r := by
    rw [Nat.mul_comm (numBlocks r) (numBuckets r)]
    exact SparseStack.numBuckets_mul_ge hr
  have hkb : 2 * (constK : ℝ) * (r : ℝ) ≤ 2 * ((numBlocks r * numBuckets r : ℕ) : ℝ) := by
    have hkbR : (constK : ℝ) * (r : ℝ) ≤ ((numBlocks r * numBuckets r : ℕ) : ℝ) := by
      exact_mod_cast hkb_nat
    linarith
  have hmain : 5 * C_H * (numBlocks r : ℝ) ^ 10 ≤
      2 * ((numBlocks r * numBuckets r : ℕ) : ℝ) := by
    have h1 : 5 * C_H * (numBlocks r : ℝ) ^ 10 ≤
        5 * C_H * ((2 * (constC : ℝ)) ^ 10 * L ^ 5) :=
      mul_le_mul_of_nonneg_left hζ10 (mul_nonneg (by norm_num) hCH.le)
    linarith
  have hζ_pos : (0 : ℝ) < (numBlocks r : ℝ) := SparseStack.numBlocks_pos_real hr
  have hb_pos : (0 : ℝ) < (numBuckets r : ℝ) := by
    have hb2 : 2 ≤ numBuckets r := SparseStack.two_le_numBuckets hr
    exact_mod_cast (show 0 < numBuckets r by omega)
  have hzb_pos : (0 : ℝ) < ((numBlocks r * numBuckets r : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_pos hζ_pos hb_pos
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (mul_pos hCH (pow_pos hζ_pos 6))]
  calc 5 * (numBlocks r : ℝ) ^ 4 * (C_H * (numBlocks r : ℝ) ^ 6)
      = 5 * C_H * (numBlocks r : ℝ) ^ 10 := by ring
    _ ≤ 1 * (2 * ((numBlocks r * numBuckets r : ℕ) : ℝ)) := by linarith

private lemma satisfiesOverlapWhp_mono
    {Ω_prob : Type} [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob)
    [MeasureTheory.IsProbabilityMeasure P] {n k : ℕ}
    (M : Ω_prob → Matrix (Fin n) (Fin k) ℝ) {η₁ η₂ p_ov : ℝ}
    (hη : η₁ ≤ η₂) (h : SatisfiesOverlapWhp P M η₁ p_ov) :
    SatisfiesOverlapWhp P M η₂ p_ov := by
  refine le_trans h (ENNReal.toReal_mono (MeasureTheory.measure_ne_top P _)
    (MeasureTheory.measure_mono ?_))
  intro ω hω
  exact le_trans hω (mul_le_mul_of_nonneg_right hη (by positivity))

/-- **Theorem 1.1 (Canonical schedule `ζ = numBlocks r`, `b = numBuckets r`, pp. 34–36).** -/
theorem theorem_1_1_Schedule : Theorem_1_1_Schedule := by
  refine ⟨constAlpha_gt, constAlpha_lt_one, SparseStack.sizeBounds_proof, ?_⟩
  intro n r hr hrn
  constructor
  · have h_outer : (fun ω : SketchSample (numBlocks r) (numBuckets r) n =>
        sparseStackOmega ω * (sparseStackOmega ω).transpose) =
      (fun ω => SparseStack.sketchOmega ω * (SparseStack.sketchOmega ω).transpose) := by
        funext ω
        exact Osi.Prelim.sparseStackOmega_outer_eq_sketchOmega ω
    rw [h_outer]
    exact SparseStack.meanIdentity_proof n r hr hrn
  · intro Q hQ
    have h_ev : (fun ω : SketchSample (numBlocks r) (numBuckets r) n =>
        MinEigenvalueAtLeast ((sparseStackOmega ω).transpose * Q) constAlpha) =
      (fun ω => SparseStack.MinEigenvalueAtLeast
        (SparseStack.sketchMatrix ω * Q) SparseStack.constAlpha) := by
        funext ω
        exact propext (Osi.Prelim.minEigenvalueAtLeast_sparseStackOmega_iff ω Q constAlpha)
    rw [h_ev]
    exact SparseStack.constantInjection_proof n r hr hrn Q hQ

/-- **Theorem 1.1 (General `(ζ, b)` form, pp. 1, 3, 34).** -/
theorem theorem_1_1_GeneralParams : Theorem_1_1_GeneralParams := by
  refine ⟨constAlpha_gt, constAlpha_lt_one, ?_⟩
  intro n r ζ b hr _hrn hb hζ hζb
  have hζ1 : 1 ≤ ζ := le_trans (by norm_num) (GenSparseStack.zeta_ge_32768 hr hζ)
  have hb1 : 1 ≤ b := by omega
  have hProb : ∀ Q : Matrix (Fin n) (Fin r) ℝ, IsIsometry Q →
      (19 / 20 : ℝ) ≤ uniformProb (SketchSample ζ b n)
        (fun ω => MinEigenvalueAtLeast ((sparseStackOmega ω).transpose * Q) constAlpha) := by
    intro Q hQ
    have h_ev : (fun ω : SketchSample ζ b n =>
        MinEigenvalueAtLeast ((sparseStackOmega ω).transpose * Q) constAlpha) =
      (fun ω => SparseStack.MinEigenvalueAtLeast
        (SparseStack.sketchMatrix ω * Q) SparseStack.constAlpha) := by
      funext ω
      exact propext (Osi.Prelim.minEigenvalueAtLeast_sparseStackOmega_iff ω Q constAlpha)
    rw [h_ev]
    exact GenSparseStack.general_constantInjection hr hb hζ hζb Q hQ
  have hOSI : IsOSI (sparseStackMeasure ζ b n)
      (sparseStackOmega (ζ := ζ) (b := b) (n := n)) r constAlpha := by
    intro Q hQ
    rw [Osi.Prelim.sparseStackMeasure_toReal_eq_uniformProb ζ b n hb1]
    exact hProb Q hQ
  exact ⟨Osi.Prelim.isProbabilityMeasure_sparseStackMeasure ζ b n hb1,
    Osi.Prelim.isRandomMatrix_sparseStackOmega ζ b n,
    Osi.Prelim.isIsotropic_sparseStackOmega ζ b n hζ1 hb1,
    Osi.Prelim.isRowSparse_sparseStackOmega ζ b n,
    hOSI,
    hProb⟩

/-- **Theorem 1.1 (Existential universal-constant `Θ(√log r)` / `Θ(r)` form, pp. 1, 3).** -/
theorem theorem_1_1_PaperRange : Theorem_1_1_PaperRange := by
  refine ⟨(constC : ℝ), (constK : ℝ), constAlpha,
    by norm_num [constC], by norm_num [constK], constAlpha_pos, constAlpha_lt_one, ?_⟩
  intro n r hr hrn C_up hCup
  set ζ := numBlocks r
  set b := numBuckets r
  have hb2 : 2 ≤ b := SparseStack.two_le_numBuckets hr
  have hζ_lo : (constC : ℝ) * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))) ≤ (ζ : ℝ) :=
    SparseStack.numBlocks_ge r
  have hζ_hi : (ζ : ℝ) ≤ C_up * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))) := by
    have h2C := numBlocks_le_two_constC_mul_sqrt hr
    have hsq0 : 0 ≤ Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))) := Real.sqrt_nonneg _
    exact le_trans h2C (mul_le_mul_of_nonneg_right hCup hsq0)
  have hζb_nat : constK * r ≤ ζ * b := by
    rw [Nat.mul_comm ζ b]
    exact SparseStack.numBuckets_mul_ge hr
  have hζb_lo : (constK : ℝ) * (r : ℝ) ≤ ((ζ * b : ℕ) : ℝ) := by
    exact_mod_cast hζb_nat
  have hζb_hi_nat : ζ * b ≤ 2 * constK * r := by
    have h1 : b * ζ ≤ (constK + constC + 1) * r :=
      le_trans (SparseStack.numBuckets_mul_le hr) (SparseStack.size_le hr)
    have h2 : constK + constC + 1 ≤ 2 * constK := by
      norm_num [constK, constC]
    calc ζ * b = b * ζ := Nat.mul_comm ζ b
      _ ≤ (constK + constC + 1) * r := h1
      _ ≤ (2 * constK) * r := Nat.mul_le_mul_right r h2
      _ = 2 * constK * r := by ring
  have hζb_hi : ((ζ * b : ℕ) : ℝ) ≤ 2 * (constK : ℝ) * (r : ℝ) := by
    exact_mod_cast hζb_hi_nat
  obtain ⟨hP, -, hIso, hSparse, hOSI, -⟩ :=
    theorem_1_1_GeneralParams.2.2 n r ζ b hr hrn hb2 hζ_lo hζb_nat
  exact ⟨ζ, b, hb2, hζ_lo, hζ_hi, hζb_lo, hζb_hi, hP, hIso, hSparse, hOSI⟩

/-- **Unified Optimal Tightness of SparseStack (Shared-Vocabulary Bridge, Section 1.1).** -/
theorem theorem_Optimal_SparseStack_Tightness : Theorem_Optimal_SparseStack_Tightness := by
  unfold Theorem_Optimal_SparseStack_Tightness
  set K_tot : ℝ := ((constK + constC + 1 : ℕ) : ℝ)
  have hKtot : 1 ≤ K_tot := by
    norm_num [K_tot, constK, constC]
  obtain ⟨c, C_H, r₀', hc, hCH, hr₀'3, hLB⟩ :=
    Osi.LowerBound.theorem_1_3_QuadraticN K_tot constAlpha hKtot constAlpha_pos constAlpha_lt_one
  set r₁ : ℕ := Nat.ceil (3 * (10 : ℝ) ^ 10 *
    (5 * C_H * (2 * (constC : ℝ)) ^ 10 / (2 * (constK : ℝ))) ^ 2)
  set r₀ : ℕ := max r₀' r₁
  refine ⟨c, C_H, r₀, hc, hCH, le_trans hr₀'3 (le_max_left _ _), ?_, ?_⟩
  · intro n r hr₀ hn
    have hr3 : 3 ≤ r := le_trans hr₀'3 (le_trans (le_max_left _ _) hr₀)
    have hr2 : 2 ≤ r := by omega
    have hrn : r ≤ n := by
      have h1 : r ≤ r * r := Nat.le_mul_self r
      have h2 : r * r ≤ 100 * r ^ 2 := by rw [sq]; omega
      exact le_trans h1 (le_trans h2 hn)
    set ζ := numBlocks r
    set b := numBuckets r
    have hb2 : 2 ≤ b := SparseStack.two_le_numBuckets hr2
    have hζ1 : 1 ≤ ζ := le_trans (by norm_num) (SparseStack.numBlocks_ge_2000 hr2)
    have hb1 : 1 ≤ b := by omega
    have hζ_lo : (constC : ℝ) * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))) ≤ (ζ : ℝ) :=
      SparseStack.numBlocks_ge r
    have hζb_nat : constK * r ≤ ζ * b := by
      rw [Nat.mul_comm ζ b]
      exact SparseStack.numBuckets_mul_ge hr2
    have hζb_tot_nat : ζ * b ≤ (constK + constC + 1) * r := by
      rw [Nat.mul_comm ζ b]
      exact le_trans (SparseStack.numBuckets_mul_le hr2) (SparseStack.size_le hr2)
    have hζb_tot : ((ζ * b : ℕ) : ℝ) ≤ K_tot * (r : ℝ) := by
      have hcast : ((ζ * b : ℕ) : ℝ) ≤ (((constK + constC + 1) * r : ℕ) : ℝ) :=
        Nat.cast_le.mpr hζb_tot_nat
      simpa only [Nat.cast_mul, K_tot] using hcast
    obtain ⟨hP, hRand, hIso, hSparse, hOSI, -⟩ :=
      theorem_1_1_GeneralParams.2.2 n r ζ b hr2 hrn hb2 hζ_lo hζb_nat
    have hOv_ss := (Osi.UpperBound.proposition_SparseStack_Overlap n ζ b hζ1 hb1).1
    have hη_le := overlap_param_le_of_large_r hCH hr2 (le_trans (le_max_right _ _) hr₀)
    have : MeasureTheory.IsProbabilityMeasure (sparseStackMeasure ζ b n) := hP
    have hOv := satisfiesOverlapWhp_mono (sparseStackMeasure ζ b n)
      (sparseStackOmega (ζ := ζ) (b := b) (n := n)) hη_le hOv_ss
    exact ⟨hζb_tot, numBlocks_le_two_constC_mul_sqrt hr2, hP, hRand, hIso, hSparse, hOv, hOSI⟩
  · intro n r k ζ hr₀ hn hk Ω_prob _inst P hP M hRand hIso hSparse hOv hOSI
    exact hLB n r k ζ (le_trans (le_max_left _ _) hr₀) hn hk Ω_prob P hP M
      hRand hIso hSparse hOv hOSI

end Osi.UpperBound
