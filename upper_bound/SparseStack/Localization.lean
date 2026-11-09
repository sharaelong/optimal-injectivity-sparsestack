import SparseStack.SmallBall
import SparseStack.Rounding
import SparseStack.Sketch.Mean
import SparseStack.Prob.Basic
import SparseStack.Loc.Basic
import SparseStack.Loc.Numerics

/-!
# Physical localization (paper, Theorem `thm:localization`, lines 351–430), `ε = 1/3`

Constants (L) with `ε = 1/3`: `η = ε/32000 = 1/96000`, `λ² = (99/100)² (2/81) ε² = 121/45000`
(`lambdaSq`), `Θ = 48800` (`locTheta`), `M = 440000` (`locM`), `m = ⌈M r/s⌉` (`locWidth r s`).

Proof outline: numerical conditions (L'); Markov on `E‖X‖_F² = r` gives `‖X‖_F² ≤ 10000 r` with
failure `≤ 1/10000`; on that event a bad unit `x` has a net center `y` (Lemma `lattice_net`) with
`d_m(Qy) ≥ ε - η` and `‖Xy‖ < λ + 50η`; top-`m` removal writes `Qy = h + a z`; with
`D = min{b, m (ε-η)²/(1+η)²}` Lemma `small_ball` applies (`sD ≥ Θ r`, `c_ph (ε-η) > λ + 50η`);
union bound over the net: `1/10000 + 2 (16/η)^r e^{-Θ r/3200} ≤ 1/10000 + 2 e^{-r} ≤ 3/20000`.

Helpers (W-LOC, namespace `SparseStack.Loc`): `center_good` (the deterministic step),
`centerEvent` / `prob_centerEvent_le` (one net center, via `topm_decomposition` and `small_ball`),
numerics in `SparseStack/Loc/Numerics.lean`.
-/

namespace SparseStack

open SparseFock

namespace Loc

/-- Deterministic step of `thm:localization`: if `‖X‖_F² < 10000 r`, a bad unit vector `x`
(`d_m(Qx)² ≥ 1/9`, `‖Xx‖² < λ²`) and a net center `y` as in `lattice_net` (with `η = 1/96000`)
satisfy `d_m(Qy)² ≥ (ε - η)²` and `‖Xy‖² < c_ph² (ε - η)²`. -/
theorem center_good {n r : ℕ} {k : Type} [Fintype k] (m : ℕ) (Q : Matrix (Fin n) (Fin r) ℝ)
    (hQ : Q.transpose * Q = 1) (X : Matrix k (Fin r) ℝ) (x y : Fin r → ℝ)
    (hx2 : 1 / 9 ≤ distSparseSq m (Q.mulVec x)) (hx3 : sqNorm (X.mulVec x) < lambdaSq)
    (hr : 1 ≤ r) (hF : frobSq X < 10000 * r) (hxy : sqNorm (x - y) ≤ (1 / 96000) ^ 2)
    (hTxy : sqNorm (X.mulVec (x - y)) ≤ (1 / 96000) ^ 2 / (4 * r) * frobSq X) :
    (1 / 3 - 1 / 96000) ^ 2 ≤ distSparseSq m (Q.mulVec y) ∧
      sqNorm (X.mulVec y) < 2 / 81 * (1 / 3 - 1 / 96000) ^ 2 := by
  constructor
  · have h1 := sqrt_distSparseSq_le m (Q.mulVec x) (Q.mulVec y)
    rw [← Matrix.mulVec_sub, sqNorm_mulVec_of_isometry Q hQ] at h1
    have h2 : √(sqNorm (x - y)) ≤ 1 / 96000 := by
      rw [Real.sqrt_le_left (by norm_num)]
      exact hxy
    have h3 : (1 / 3 : ℝ) ≤ √(distSparseSq m (Q.mulVec x)) := by
      rw [Real.le_sqrt (by norm_num) (distSparseSq_nonneg _ _)]
      have h9 : (1 / 3 : ℝ) ^ 2 = 1 / 9 := by norm_num
      rw [h9]
      exact hx2
    have h4 : (1 / 3 - 1 / 96000 : ℝ) ≤ √(distSparseSq m (Q.mulVec y)) := by linarith
    have h5 := pow_le_pow_left₀ (by norm_num) h4 2
    rwa [Real.sq_sqrt (distSparseSq_nonneg _ _)] at h5
  · have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have h1 : √(sqNorm (X.mulVec y)) ≤
        √(sqNorm (X.mulVec x)) + √(sqNorm (X.mulVec (x - y))) := by
      have h := sqrt_sqNorm_sub_le (X.mulVec x) (X.mulVec (x - y))
      rwa [show X.mulVec x - X.mulVec (x - y) = X.mulVec y by
        rw [Matrix.mulVec_sub, sub_sub_cancel]] at h
    have h2 : sqNorm (X.mulVec (x - y)) ≤ (50 * (1 / 96000)) ^ 2 := by
      calc sqNorm (X.mulVec (x - y)) ≤ (1 / 96000) ^ 2 / (4 * r) * frobSq X := hTxy
        _ ≤ (1 / 96000) ^ 2 / (4 * r) * (10000 * r) :=
          mul_le_mul_of_nonneg_left hF.le (by positivity)
        _ = (50 * (1 / 96000)) ^ 2 := by
          field_simp
          ring
    have h3 : √(sqNorm (X.mulVec (x - y))) ≤ 50 * (1 / 96000) := by
      rw [Real.sqrt_le_left (by norm_num)]
      exact h2
    have h4 : √(sqNorm (X.mulVec x)) < 51855 / 1000000 := by
      calc √(sqNorm (X.mulVec x)) < √lambdaSq := Real.sqrt_lt_sqrt (sqNorm_nonneg _) hx3
        _ ≤ 51855 / 1000000 := by
          unfold lambdaSq
          exact sqrt_lambdaSq_le
    have h5 : √(sqNorm (X.mulVec y)) < 51855 / 1000000 + 50 * (1 / 96000) := by linarith
    have h6 : sqNorm (X.mulVec y) < (51855 / 1000000 + 50 * (1 / 96000)) ^ 2 := by
      rwa [Real.sqrt_lt' (by norm_num)] at h5
    exact lt_of_lt_of_le h6 loc_lambda_check

/-- The bad event of one net center `y`: `d_m(Qy)² ≥ (ε - η)²` and `‖Π Q y‖² < c_ph² (ε - η)²`. -/
def centerEvent {n r : ℕ} (s b m : ℕ) (Q : Matrix (Fin n) (Fin r) ℝ) (y : Fin r → ℝ) :
    Set (SketchSample s b n) :=
  {ω | (1 / 3 - 1 / 96000 : ℝ) ^ 2 ≤ distSparseSq m (Q.mulVec y) ∧
    sqNorm ((sketchMatrix ω * Q).mulVec y) < 2 / 81 * (1 / 3 - 1 / 96000) ^ 2}

/-- One net center (paper, lines 404–422): top-`m` removal and Lemma `small_ball` with
`D = min{b, m (ε-η)²/(1+η)²}` give `P(centerEvent) ≤ 2 e^{-Θ r/3200}`. -/
theorem prob_centerEvent_le {n r s b m : ℕ} (hs : 0 < s) (hb : 0 < b) (hsr : s ≤ r)
    (hsm : (440000 : ℝ) * r ≤ s * m) (hbs : (48800 : ℝ) * r ≤ b * s)
    (Q : Matrix (Fin n) (Fin r) ℝ) (hQ : Q.transpose * Q = 1)
    (y : Fin r → ℝ) (hy : sqNorm y ≤ (1 + 1 / 96000) ^ 2) :
    (sketchLaw s b n hb).prob (centerEvent s b m Q y) ≤
      2 * Real.exp (-((48800 : ℝ) * r) / 3200) := by
  by_cases hd : (1 / 3 - 1 / 96000 : ℝ) ^ 2 ≤ distSparseSq m (Q.mulVec y)
  · have hdpos : 0 < distSparseSq m (Q.mulVec y) := lt_of_lt_of_le (by norm_num) hd
    obtain ⟨h, z, hw, hdisj, hz, hzi⟩ := topm_decomposition m (Q.mulVec y) hdpos
    generalize hd_def : distSparseSq m (Q.mulVec y) = d at hd hdpos hw hzi
    have ha : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
    have ha2 : Real.sqrt d ^ 2 = d := Real.sq_sqrt hdpos.le
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hs0 (by exact_mod_cast hsr)
    have hsr' : (s : ℝ) ≤ r := by exact_mod_cast hsr
    have hmM : (440000 : ℝ) ≤ m := by
      by_contra hcon
      push Not at hcon
      have h1 : (s : ℝ) * m < s * 440000 := mul_lt_mul_of_pos_left hcon hs0
      nlinarith
    have hc0 : (0 : ℝ) < (1 / 3 - 1 / 96000) ^ 2 / (1 + 1 / 96000) ^ 2 := by norm_num
    have hcM := loc_M_check
    obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = (1 / 3 - 1 / 96000) ^ 2 / (1 + 1 / 96000) ^ 2 := ⟨_, rfl⟩
    rw [← hc_def] at hc0 hcM
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have hmc1 : (1 : ℝ) ≤ m * c := by nlinarith
    obtain ⟨D, hD_def⟩ : ∃ D : ℝ, D = min (b : ℝ) (m * c) := ⟨_, rfl⟩
    have hD1 : 1 ≤ D := by rw [hD_def]; exact le_min hb1 hmc1
    have hDb : D ≤ b := by rw [hD_def]; exact min_le_left _ _
    have hDmc : D ≤ m * c := by rw [hD_def]; exact min_le_right _ _
    have hzinf : ∀ i, z i ^ 2 ≤ 1 / D := by
      intro i
      have hD0 : 0 < D := by linarith
      rw [le_div_iff₀ hD0]
      have h1 := hzi i
      rw [sqNorm_mulVec_of_isometry Q hQ] at h1
      have hzi2 : 0 ≤ z i ^ 2 := sq_nonneg _
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      have hη2 : (0 : ℝ) < (1 + 1 / 96000) ^ 2 := by norm_num
      calc z i ^ 2 * D ≤ z i ^ 2 * (m * c) := mul_le_mul_of_nonneg_left hDmc hzi2
        _ = m * (1 / 3 - 1 / 96000) ^ 2 * z i ^ 2 / (1 + 1 / 96000) ^ 2 := by
          rw [hc_def]
          ring
        _ ≤ m * d * z i ^ 2 / (1 + 1 / 96000) ^ 2 := by gcongr
        _ ≤ sqNorm y / (1 + 1 / 96000) ^ 2 := by gcongr
        _ ≤ 1 := by
          rw [div_le_one hη2]
          exact hy
    have hsD : (48800 : ℝ) * r ≤ s * D := by
      have hmc : (48800 : ℝ) * r ≤ s * (m * c) := by
        calc (48800 : ℝ) * r ≤ (440000 * c) * r := mul_le_mul_of_nonneg_right hcM hr0.le
          _ = (440000 * r) * c := by ring
          _ ≤ (s * m) * c := mul_le_mul_of_nonneg_right hsm hc0.le
          _ = s * (m * c) := by ring
      rcases le_total (b : ℝ) (m * c) with hle | hle
      · rw [hD_def, min_eq_left hle]
        linarith
      · rw [hD_def, min_eq_right hle]
        exact hmc
    have hSB := small_ball hs hb h z (Real.sqrt d) ha hdisj hz D hD1 hDb hzinf
    calc (sketchLaw s b n hb).prob (centerEvent s b m Q y)
        ≤ (sketchLaw s b n hb).prob
          {ω | sqNorm ((sketchMatrix ω).mulVec (h + Real.sqrt d • z)) <
            2 / 81 * Real.sqrt d ^ 2} := by
          apply FiniteLaw.prob_mono
          intro ω hω
          obtain ⟨_, hω2⟩ := hω
          show sqNorm ((sketchMatrix ω).mulVec (h + Real.sqrt d • z)) < 2 / 81 * Real.sqrt d ^ 2
          rw [← hw, Matrix.mulVec_mulVec, ha2]
          linarith
      _ ≤ 2 * Real.exp (-((s : ℝ) * D) / 3200) := hSB
      _ ≤ 2 * Real.exp (-((48800 : ℝ) * r) / 3200) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          linarith
  · have hempty : centerEvent s b m Q y = ∅ := by
      ext ω
      simp only [centerEvent, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h
      exact absurd h hd
    rw [hempty, FiniteLaw.prob_empty]
    positivity

end Loc

/-- Theorem `thm:localization` with `ε = 1/3`: for `r ≥ 11`, `1 ≤ s ≤ r`, `b s ≥ Θ r` and a fixed
isometry `Q`, with probability at least `1 - 3/20000` every unit `x` with `d_m(Qx) ≥ 1/3` has
`‖Π_{s,b} Q x‖² ≥ λ²`, where `m = ⌈M r/s⌉`. -/
theorem localization {n r s b : ℕ} (hr : 11 ≤ r) (hs : 1 ≤ s) (hsr : s ≤ r) (hb : 0 < b)
    (hbs : locTheta * r ≤ b * s) (Q : Matrix (Fin n) (Fin r) ℝ) (hQ : Q.transpose * Q = 1) :
    (sketchLaw s b n hb).prob
        {ω | ∃ x : Fin r → ℝ, sqNorm x = 1 ∧ 1 / 9 ≤ distSparseSq (locWidth r s) (Q.mulVec x) ∧
          sqNorm ((sketchMatrix ω * Q).mulVec x) < lambdaSq} ≤ 3 / 20000 := by
  obtain ⟨N, hNcard, hNnorm, hNround⟩ :=
    lattice_net r (by omega) (1 / 96000) (by norm_num) (by norm_num)
  have hr1 : 1 ≤ r := by omega
  have hs0' : 0 < s := by omega
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs0'
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  -- the width `m = ⌈M r / s⌉` satisfies `s m ≥ M r`
  have hsm : (440000 : ℝ) * r ≤ s * (locWidth r s : ℝ) := by
    have h1 : (locM : ℝ) * r / s ≤ (locWidth r s : ℝ) := Nat.le_ceil _
    have h2 : (locM : ℝ) = 440000 := by norm_num [locM]
    rw [h2, div_le_iff₀ hs0] at h1
    linarith
  have hbs' : (48800 : ℝ) * r ≤ b * s := by
    have h1 : ((locTheta * r : ℕ) : ℝ) ≤ ((b * s : ℕ) : ℝ) := by exact_mod_cast hbs
    push_cast at h1
    have h2 : (locTheta : ℝ) = 48800 := by norm_num [locTheta]
    rw [h2] at h1
    exact h1
  -- the event inclusion
  have hsub : {ω : SketchSample s b n | ∃ x : Fin r → ℝ, sqNorm x = 1 ∧
      1 / 9 ≤ distSparseSq (locWidth r s) (Q.mulVec x) ∧
      sqNorm ((sketchMatrix ω * Q).mulVec x) < lambdaSq} ⊆
      {ω | (10000 * r : ℝ) ≤ frobSq (sketchMatrix ω * Q)} ∪
        ⋃ y ∈ N, Loc.centerEvent s b (locWidth r s) Q y := by
    intro ω hω
    obtain ⟨x, hx1, hx2, hx3⟩ := hω
    by_cases hF : (10000 * r : ℝ) ≤ frobSq (sketchMatrix ω * Q)
    · exact Or.inl hF
    · right
      push Not at hF
      obtain ⟨y, hyN, hxy, hTxy⟩ := hNround (Fin s × Fin b) (sketchMatrix ω * Q) x hx1
      rw [Set.mem_iUnion₂]
      exact ⟨y, hyN, Loc.center_good (locWidth r s) Q hQ (sketchMatrix ω * Q) x y hx2 hx3 hr1 hF
        hxy hTxy⟩
  -- Markov: `P{‖Π Q‖_F² ≥ 10000 r} ≤ 1/10000`
  have hF₁ : (sketchLaw s b n hb).prob {ω | (10000 * r : ℝ) ≤ frobSq (sketchMatrix ω * Q)} ≤
      1 / 10000 := by
    have hmk := FiniteLaw.markov (sketchLaw s b n hb)
      (f := fun ω => frobSq (sketchMatrix ω * Q)) (fun ω => Loc.frobSq_nonneg _)
      (threshold := 10000 * r) (by positivity)
    rw [expect_frobSq (s := s) hs0' hb Q hQ] at hmk
    calc (sketchLaw s b n hb).prob {ω | (10000 * r : ℝ) ≤ frobSq (sketchMatrix ω * Q)}
        ≤ (r : ℝ) / (10000 * r) := hmk
      _ = 1 / 10000 := by field_simp
  -- one net center
  have hE : ∀ y ∈ N, (sketchLaw s b n hb).prob (Loc.centerEvent s b (locWidth r s) Q y) ≤
      2 * Real.exp (-((48800 : ℝ) * r) / 3200) :=
    fun y hy => Loc.prob_centerEvent_le hs0' hb hsr hsm hbs' Q hQ y (hNnorm y hy)
  have hnet := Loc.net_exp_le r
  have hr11 : Real.exp (-(r : ℝ)) ≤ Real.exp (-11) := by
    apply Real.exp_le_exp.mpr
    have : (11 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have h11 := Loc.two_exp_neg_eleven_le
  have hexp0 : 0 ≤ 2 * Real.exp (-((48800 : ℝ) * r) / 3200) := by positivity
  refine le_trans ((sketchLaw s b n hb).prob_mono hsub) ?_
  calc (sketchLaw s b n hb).prob
        ({ω | (10000 * r : ℝ) ≤ frobSq (sketchMatrix ω * Q)} ∪
          ⋃ y ∈ N, Loc.centerEvent s b (locWidth r s) Q y)
      ≤ (sketchLaw s b n hb).prob {ω | (10000 * r : ℝ) ≤ frobSq (sketchMatrix ω * Q)} +
          (sketchLaw s b n hb).prob (⋃ y ∈ N, Loc.centerEvent s b (locWidth r s) Q y) :=
        prob_union_le _ _ _
    _ ≤ 1 / 10000 + ∑ y ∈ N, (sketchLaw s b n hb).prob (Loc.centerEvent s b (locWidth r s) Q y) :=
        add_le_add hF₁ (prob_union_le_sum _ N _)
    _ ≤ 1 / 10000 + ∑ _y ∈ N, 2 * Real.exp (-((48800 : ℝ) * r) / 3200) := by
        gcongr with y hy
        exact hE y hy
    _ = 1 / 10000 + (N.card : ℝ) * (2 * Real.exp (-((48800 : ℝ) * r) / 3200)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 / 10000 + (16 / (1 / 96000)) ^ r * (2 * Real.exp (-((48800 : ℝ) * r) / 3200)) := by
        gcongr
    _ = 1 / 10000 + 2 * ((16 / (1 / 96000)) ^ r * Real.exp (-((48800 : ℝ) * r) / 3200)) := by
        ring
    _ ≤ 1 / 10000 + 2 * Real.exp (-(r : ℝ)) := by gcongr
    _ ≤ 3 / 20000 := by linarith

end SparseStack
