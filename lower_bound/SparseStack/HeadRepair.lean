import SparseStack.CrossGram
import SparseStack.Sketch.Mean
import SparseStack.Prob.Toolkit
import SparseStack.Repair.Numerics
import SparseStack.Repair.Assembly
import SparseStack.Repair.CrossProb

/-!
# Independent-background coordinate-head repair (paper, Theorem `thm:head-repair`, lines 871–1111)

Specialized to the constants of thm:main: `ρ₀ = 499/1000`, `H_rep = 256`, `a₀ = 11/12`,
`δ_cross = 249/10000`, `δ_ret = 1/40000`, `t₀ = 11/48`, `β = ρ₀(a₀ - 2t₀) = 5489/24000`,
`C⋆ = 255232512/15625`, `K⋆ = 79840000` (conditions (R1)–(R3) hold for these).

Only the regime `q < H_rep log(eR)` is needed: in thm:main, `q = ⌊ζ/2⌋ < 52 L ≤ 52 log(eR)`.

Statement in **variational form** (this is how the paper uses it, via eq. (variational)):
with probability `≥ 1 - 997/20000`, for all `h` supported on `I` and all `f`,
`β ‖h‖² ≤ ‖Π (h + V f)‖² + t₀ ‖f‖²`, where the background `V ∈ ℝ^{n×d}` is a fixed isometry
supported off `I` (the paper's `Z = Π_{q,b,J} W`, `C = Π_{q,b,I}`).

Proof outline (regime `q < H_rep L_R`): `s = ⌊q/2⌋`, `p = ⌈log(2eR)⌉`; numerics (`ρ₀ q ≤ s`,
`L_R > 64`, `R ≥ 300 L_R`, `p ≥ 64`, `p ≥ log(2d)` for `d ≤ 2R`, `p + 1 ≤ (67/64) L_R`,
`N + D_p ≤ (301/100) R`, `b/s > 2`); `cross_gram_refined` + Markov gives
`P{‖H̃ᵀỸ‖ > t₀ | head} ≤ E⋆/t₀ ≤ δ_cross` (eq. (cross-probability)); two disjoint `s`-block groups;
group 1: retained head Gram `diag(a_i/s)`, good set `G = {a_i ≥ a₀ s}`, `B = I \ G`,
`P{|B| > N e^{-s/2304}} < δ_ret`; first certificate (eq. (first-certificate)); group 2 with head
`B` and background `diag(I_G, V)` (dimension `≤ 2R`): subset bound and union bound `< δ_ret`,
second certificate (eq. (second-certificate)); add; normalization `s/q ∈ [ρ₀, 1/2]`;
failures `2 δ_cross + 2 δ_ret = 997/20000`.
-/

namespace SparseStack

open SparseFock
open scoped Matrix.Norms.L2Operator

/-- Theorem `thm:head-repair` (regime `q < H_rep log(eR)`, variational form, thm:main constants). -/
theorem head_repair {n R q b d : ℕ} (hR : 2 ≤ R) (hb : 0 < b)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) (hbq : kStarRep * R ≤ b * q)
    (I : Finset (Fin n)) (hIR : I.card ≤ R) (hIb : 16 * I.card ≤ b)
    (V : Matrix (Fin n) (Fin d) ℝ) (hV : V.transpose * V = 1)
    (hVsupp : ∀ i ∈ I, ∀ k, V i k = 0) (hdR : d ≤ R) :
    1 - 997 / 20000 ≤ (sketchLaw q b n hb).prob
      {ω | ∀ h : Fin n → ℝ, (∀ i, i ∉ I → h i = 0) → ∀ f : Fin d → ℝ,
        betaRep * sqNorm h ≤ sqNorm ((sketchMatrix ω).mulVec (h + V.mulVec f)) + t0 * sqNorm f} := by
  classical
  /- Parameters `s = ⌊q/2⌋`, `p = ⌈log(2eR)⌉` and their numerics (HR1). -/
  set s : ℕ := q / 2 with hs_def
  set p : ℕ := ⌈Real.log (2 * Real.exp 1 * R)⌉₊ with hp_def
  have hs_gt : (500000 : ℝ) < s := rep_s_gt hR hq hqreg
  have hs1 : 1 ≤ s := by
    have : (1 : ℝ) ≤ s := by linarith
    exact_mod_cast this
  have hs0 : 0 < s := hs1
  have h2s : 2 * s ≤ q := Nat.mul_div_le q 2
  have hbs : 2 * s ≤ b := le_trans h2s (rep_q_le_b hR hq hqreg hbq)
  have hp64 : 64 ≤ p := rep_p_ge hR hq hqreg
  have hexp : Real.exp (-(s : ℝ) / 2304) < 1 / 40000 := rep_exp_lt hR hq hqreg
  have hret2 : (R : ℝ) * ((2 : ℝ) ^ s * (Real.exp (-(s : ℝ) / 2304) / 16) ^ ((s : ℝ) / 12)) <
      1 / 40000 := rep_retention2_lt hR hq hqreg
  have hcb : ∀ N d' : ℕ, N ≤ R → 16 * N ≤ b → d' ≤ 2 * R →
      crossBound N d' p b s ≤ 249 / 10000 * t0 :=
    fun N d' hN hNb hd' => rep_crossBound_le hR hq hqreg hbq hN hNb hd'
  have hplog : ∀ d' : ℕ, d' ≤ 2 * R → 1 ≤ d' → Real.log (2 * d') ≤ p :=
    fun d' hd' hd1 => rep_log_le_p hR hd1 hd'
  have hq0 : (0 : ℝ) < q := by
    have := rep_q_gt hR hq hqreg
    linarith
  have hcge : rho0 ≤ (s : ℝ) / q := (le_div_iff₀ hq0).2 (rep_s_ge hR hq hqreg)
  have hcle : (s : ℝ) / q ≤ 1 / 2 := by
    rw [div_le_iff₀ hq0]
    have := rep_s_le q
    linarith
  /- The two disjoint groups: blocks `0, …, s-1` and `s, …, 2s-1`. -/
  let f₁ : Fin s → Fin q := fun t => ⟨t.1, by have := t.isLt; omega⟩
  let f₂ : Fin s → Fin q := fun t => ⟨s + t.1, by have := t.isLt; omega⟩
  have hf₁ : Function.Injective f₁ := by
    intro t t' htt
    have := congrArg Fin.val htt
    exact Fin.ext this
  have hf₂ : Function.Injective f₂ := by
    intro t t' htt
    have h' : s + t.1 = s + t'.1 := congrArg Fin.val htt
    exact Fin.ext (by omega)
  have hdisj : ∀ t₁ t₂, f₁ t₁ ≠ f₂ t₂ := by
    intro t₁ t₂ htt
    have h' : t₁.1 = s + t₂.1 := congrArg Fin.val htt
    have := t₁.isLt
    omega
  /- Group 1: cross-Gram success and few bad coordinates. Group 2: cross-Gram success for the
  head `B` against `W₊ = [E_G | V]`, and full retention of `B`. -/
  let E₁ : SketchSample s b n → Prop := fun ω₁ =>
    ‖crossGram I V ω₁‖ ≤ t0 ∧
      ((badSet I ω₁).card : ℝ) ≤ I.card * Real.exp (-(s : ℝ) / 2304)
  let E₂ : SketchSample s b n → SketchSample s b n → Prop := fun ω₁ ω₂ =>
    ‖crossGram (badSet I ω₁) (wPlus (goodSet I ω₁) V) ω₂‖ ≤ t0 ∧
      ∀ i ∈ badSet I ω₁, a0 * s ≤ retCount (badSet I ω₁) ω₂ i
  /- First stage: failure `≤ δ_cross + δ_ret`. -/
  have h₁ : 1 - (249 / 10000 + 1 / 40000) ≤ (sketchLaw s b n hb).prob {ω₁ | E₁ ω₁} := by
    apply one_sub_le_prob_of_prob_compl_le
    have hsub : {ω₁ | E₁ ω₁}ᶜ ⊆ {ω | t0 < ‖crossGram I V ω‖} ∪
        {ω | (I.card : ℝ) * Real.exp (-(s : ℝ) / 2304) < (badSet I ω).card} := by
      intro ω hω
      have hω' : ¬ (‖crossGram I V ω‖ ≤ t0 ∧
          ((badSet I ω).card : ℝ) ≤ I.card * Real.exp (-(s : ℝ) / 2304)) := hω
      rcases not_and_or.1 hω' with h | h
      · exact Or.inl (not_le.1 h)
      · exact Or.inr (not_le.1 h)
    have hc := cross_prob hb hs1 hbs hp64 I V hV hVsupp (hplog d (by omega))
      (hcb I.card d hIR hIb (by omega))
    have hB := prob_badSet_card_le hb hs1 I hIb
    calc (sketchLaw s b n hb).prob {ω₁ | E₁ ω₁}ᶜ
        ≤ (sketchLaw s b n hb).prob ({ω | t0 < ‖crossGram I V ω‖} ∪
            {ω | (I.card : ℝ) * Real.exp (-(s : ℝ) / 2304) < (badSet I ω).card}) :=
          FiniteLaw.prob_mono _ hsub
      _ ≤ _ := prob_union_le _ _ _
      _ ≤ 249 / 10000 + 1 / 40000 := by linarith
  /- Second stage, conditionally on any first-stage outcome in `E₁`: failure
  `≤ δ_cross + δ_ret`. -/
  have h₂ : ∀ ω₁, E₁ ω₁ →
      1 - (249 / 10000 + 1 / 40000) ≤ (sketchLaw s b n hb).prob {ω₂ | E₂ ω₁ ω₂} := by
    intro ω₁ hE₁
    have hBI : badSet I ω₁ ⊆ I := badSet_subset I ω₁
    have hGI : goodSet I ω₁ ⊆ I := goodSet_subset I ω₁
    have hBG : Disjoint (badSet I ω₁) (goodSet I ω₁) := disjoint_badSet_goodSet I ω₁
    have hBcardI : (badSet I ω₁).card ≤ I.card := Finset.card_le_card hBI
    have hGcardI : (goodSet I ω₁).card ≤ I.card := Finset.card_le_card hGI
    apply one_sub_le_prob_of_prob_compl_le
    have hsub : {ω₂ | E₂ ω₁ ω₂}ᶜ ⊆
        {ω | t0 < ‖crossGram (badSet I ω₁) (wPlus (goodSet I ω₁) V) ω‖} ∪
        {ω | ∃ i ∈ badSet I ω₁, (retCount (badSet I ω₁) ω i : ℝ) < a0 * s} := by
      intro ω hω
      have hω' : ¬ (‖crossGram (badSet I ω₁) (wPlus (goodSet I ω₁) V) ω‖ ≤ t0 ∧
          ∀ i ∈ badSet I ω₁, a0 * s ≤ retCount (badSet I ω₁) ω i) := hω
      rcases not_and_or.1 hω' with h | h
      · exact Or.inl (not_le.1 h)
      · push Not at h
        exact Or.inr h
    have hc := cross_prob hb hs1 hbs hp64 (badSet I ω₁) (wPlus (goodSet I ω₁) V)
      (wPlus_isometry (goodSet I ω₁) V hV (fun i hi => hVsupp i (hGI hi)))
      (wPlus_supp (badSet I ω₁) (goodSet I ω₁) hBG V (fun i hi => hVsupp i (hBI hi)))
      (hplog _ (by omega))
      (hcb _ _ (le_trans hBcardI hIR) (le_trans (Nat.mul_le_mul_left 16 hBcardI) hIb)
        (by omega))
    have hBcard : 16 * ((badSet I ω₁).card : ℝ) ≤ b * Real.exp (-(s : ℝ) / 2304) := by
      have h1 : ((badSet I ω₁).card : ℝ) ≤ I.card * Real.exp (-(s : ℝ) / 2304) := hE₁.2
      have h2 : (16 * I.card : ℝ) ≤ b := by exact_mod_cast hIb
      have he : 0 ≤ Real.exp (-(s : ℝ) / 2304) := (Real.exp_pos _).le
      nlinarith
    have hr := prob_retention2_le hb hs1 (badSet I ω₁) hBcard
    have hBR : ((badSet I ω₁).card : ℝ) ≤ R := by exact_mod_cast le_trans hBcardI hIR
    have hpos : 0 ≤ (2 : ℝ) ^ s * (Real.exp (-(s : ℝ) / 2304) / 16) ^ ((s : ℝ) / 12) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_right hBR hpos
    calc (sketchLaw s b n hb).prob {ω₂ | E₂ ω₁ ω₂}ᶜ
        ≤ (sketchLaw s b n hb).prob
            ({ω | t0 < ‖crossGram (badSet I ω₁) (wPlus (goodSet I ω₁) V) ω‖} ∪
              {ω | ∃ i ∈ badSet I ω₁, (retCount (badSet I ω₁) ω i : ℝ) < a0 * s}) :=
          FiniteLaw.prob_mono _ hsub
      _ ≤ _ := prob_union_le _ _ _
      _ ≤ 249 / 10000 + 1 / 40000 := by linarith
  /- Two-stage independence of the disjoint groups. -/
  have key := two_stage_independence hb f₁ f₂ hf₁ hf₂ hdisj E₁ E₂
    (δ₁ := 249 / 10000 + 1 / 40000) (δ₂ := 249 / 10000 + 1 / 40000) (by norm_num) h₁ h₂
  refine le_trans (le_of_eq (by norm_num)) (le_trans key (FiniteLaw.prob_mono _ ?_))
  /- On the joint event: add the two certificates and use the group inequality. -/
  rintro ω ⟨hE₁, hE₂⟩ h hh f
  have hBG : Disjoint (badSet I (blockRestrict f₁ ω)) (goodSet I (blockRestrict f₁ ω)) :=
    disjoint_badSet_goodSet I _
  have hh' : ∀ i, i ∉ badSet I (blockRestrict f₁ ω) ∪ goodSet I (blockRestrict f₁ ω) →
      h i = 0 := by
    intro i hi
    rw [badSet_union_goodSet] at hi
    exact hh i hi
  have c1 := first_certificate hs0 I V (blockRestrict f₁ ω) hE₁.1 h hh f
  have c2 := second_certificate hs0 _ _ hBG V (blockRestrict f₂ ω) hE₂.1 hE₂.2 h hh' f
  have grp := sqNorm_sketch_ge_groups f₁ f₂ hf₁ hf₂ hdisj ω (h + V.mulVec f)
  have hsplit := sqNorm_eq_good_add_bad I (blockRestrict f₁ ω) h hh
  set X₁ := sqNorm ((sketchMatrix (blockRestrict f₁ ω)).mulVec (h + V.mulVec f))
  set X₂ := sqNorm ((sketchMatrix (blockRestrict f₂ ω)).mulVec (h + V.mulVec f))
  set X := sqNorm ((sketchMatrix ω).mulVec (h + V.mulVec f))
  set SG := ∑ i ∈ goodSet I (blockRestrict f₁ ω), h i ^ 2
  set SB := ∑ i ∈ badSet I (blockRestrict f₁ ω), h i ^ 2
  set c : ℝ := (s : ℝ) / q
  have hSG : 0 ≤ SG := Finset.sum_nonneg (fun i _ => sq_nonneg (h i))
  have hSB : 0 ≤ SB := Finset.sum_nonneg (fun i _ => sq_nonneg (h i))
  have hF : 0 ≤ sqNorm f := rep_sqNorm_nonneg f
  have hc0 : 0 ≤ c := le_trans (by norm_num [rho0]) hcge
  have hsum : 11 / 24 * (SG + SB) ≤ X₁ + X₂ + 11 / 24 * sqNorm f := by
    simp only [a0, t0] at c1 c2
    linarith
  have k1 := mul_le_mul_of_nonneg_left hsum hc0
  have k2 := mul_le_mul_of_nonneg_right hcge (by positivity : (0 : ℝ) ≤ 11 / 24 * (SG + SB))
  have k3 := mul_le_mul_of_nonneg_right hcle (by positivity : (0 : ℝ) ≤ 11 / 24 * sqNorm f)
  rw [hsplit]
  simp only [betaRep, t0, rho0] at k2 ⊢
  linarith

end SparseStack
