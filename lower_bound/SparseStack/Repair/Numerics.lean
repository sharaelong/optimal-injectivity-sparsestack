import SparseStack.Repair.Defs
import SparseStack.Numerics.RepairNum

/-!
# Head repair, numerics (HR1) (paper, lines 977–1017, 1044–1084)

Regime hypotheses (those of `head_repair`): `R ≥ 2`, `C⋆ √L ≤ q < 256 L` and `K⋆ R ≤ b q`, where
`L = L_R = log(eR)`, `C⋆ = cStarRep`, `K⋆ = kStarRep`. Parameters: `s = ⌊q/2⌋`,
`p = ⌈log(2eR)⌉`.

Key observation: `C⋆ √L < 256 L` forces `√L > C⋆/256 > 63.8`, i.e. `L > 4071`; hence `q > 10⁶`,
`s > 5·10⁵` and `R = e^{L-1}` is astronomically large. All facts below follow from this, from
`R ≥ e^{L-1} ≥ (L-1)⁴/24` and from the exact rational certificate `E⋆ ≤ δ_cross t₀`.

* `rep_L_gt`: `4071 < L`;
* `rep_q_gt`: `10⁶ < q`; `rep_s_gt`: `5·10⁵ < s`; `rep_s_ge`: `ρ₀ q ≤ s`; `rep_s_le`: `s ≤ q/2`;
* `rep_R_ge`: `300 L ≤ R`; `rep_L_cube_le`: `L³ ≤ 4 R`;
* `rep_q_le_b`: `q ≤ b` (so `2 s ≤ b`, i.e. `b/s ≥ 2`);
* `rep_p_ge`: `64 ≤ p`; `rep_log_le_p`: `log(2d') ≤ p` for `1 ≤ d' ≤ 2R`;
* `estar_le`: `E⋆ = 22 √(301/(150ρ₀K⋆) + 67/(64ρ₀²C⋆²)) + 2900/K⋆ ≤ δ_cross t₀` (rational);
* `rep_crossBound_le`: the right-hand side of eq. (refined-cross) is `≤ δ_cross t₀` for every
  head size `N ≤ min(R, b/16)` and background dimension `d' ≤ 2R`;
* `rep_exp_lt`: `e^{-s/2304} < δ_ret`;
* `rep_retention2_lt`: `R · 2^s (e^{-s/2304}/16)^{s/12} < δ_ret`.

The proofs are applications of the general certificates in `SparseStack/Numerics/RepairNum.lean`
(W-NUM).
-/

namespace SparseStack

open Real

/-- `L = log(eR) > 4071` in the regime `C⋆ √L ≤ q < 256 L`. -/
theorem rep_L_gt {R q : ℕ} (hR : 2 ≤ R)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) :
    4071 < Real.log (Real.exp 1 * R) := by
  have _hR2 : 2 ≤ R := hR
  exact repnum_regime_L_gt hq hqreg

/-- `q > 10⁶`. -/
theorem rep_q_gt {R q : ℕ} (hR : 2 ≤ R)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) :
    1000000 < (q : ℝ) := by
  have _hR2 : 2 ≤ R := hR
  have h := repnum_regime_q_gt hq hqreg
  linarith

/-- `s = ⌊q/2⌋ ≤ q/2`. -/
theorem rep_s_le (q : ℕ) : ((q / 2 : ℕ) : ℝ) ≤ (q : ℝ) / 2 := by
  exact Nat.cast_div_le

/-- `ρ₀ q ≤ s` (as `q ≥ 500`). -/
theorem rep_s_ge {R q : ℕ} (hR : 2 ≤ R)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) :
    rho0 * q ≤ ((q / 2 : ℕ) : ℝ) := by
  have h := rep_q_gt hR hq hqreg
  have hq500 : 500 ≤ q := by
    have : (500 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hsN : 499 * q ≤ 1000 * (q / 2) := by omega
  have hsR : (499 : ℝ) * q ≤ 1000 * ((q / 2 : ℕ) : ℝ) := by exact_mod_cast hsN
  unfold rho0
  linarith

/-- `s > 5·10⁵`. -/
theorem rep_s_gt {R q : ℕ} (hR : 2 ≤ R)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) :
    500000 < ((q / 2 : ℕ) : ℝ) := by
  have _hR2 : 2 ≤ R := hR
  have h := repnum_regime_q_gt hq hqreg
  have hq' : 1040000 < q := by exact_mod_cast h
  have hs : 500000 < q / 2 := by omega
  exact_mod_cast hs

/-- `R ≥ 300 L` (from `R = e^{L-1} ≥ (L-1)⁴/24`). -/
theorem rep_R_ge {R q : ℕ} (hR : 2 ≤ R)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) :
    300 * Real.log (Real.exp 1 * R) ≤ R := by
  have hL := rep_L_gt hR hq hqreg
  have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
  exact repnum_R_ge_300 (by linarith) (by linarith)

/-- `L³ ≤ 4 R` (from `R = e^{L-1} ≥ (L-1)⁴/24`). -/
theorem rep_L_cube_le {R q : ℕ} (hR : 2 ≤ R)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) :
    Real.log (Real.exp 1 * R) ^ 3 ≤ 4 * R := by
  have _hq := hq
  have _hqreg := hqreg
  have hR1 : (1 : ℝ) ≤ R := by
    have : (2 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  exact repnum_L_cube_le hR1

/-- `q ≤ b` (as `q² < 65536 L² ≤ K⋆ R ≤ b q`); in particular `2 s ≤ b`. -/
theorem rep_q_le_b {R q b : ℕ} (hR : 2 ≤ R)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) (hbq : kStarRep * R ≤ b * q) :
    q ≤ b := by
  have hqgt := rep_q_gt hR hq hqreg
  have hR1 : (1 : ℝ) ≤ R := by
    have : (2 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hL2 := repnum_L_sq_le hR1
  have hq0 : (0 : ℝ) < q := by linarith
  have hbqR : (kStarRep : ℝ) * R ≤ b * q := by exact_mod_cast hbq
  rw [repnum_kStar_real] at hbqR
  have hq2 : (q : ℝ) ^ 2 < (256 * Real.log (Real.exp 1 * R)) ^ 2 :=
    pow_lt_pow_left₀ hqreg hq0.le (by norm_num)
  have h1 : (q : ℝ) * q < b * q := by nlinarith
  have h2 : (q : ℝ) < b := lt_of_mul_lt_mul_right h1 hq0.le
  exact_mod_cast h2.le

/-- `p = ⌈log(2eR)⌉ ≥ 64`. -/
theorem rep_p_ge {R q : ℕ} (hR : 2 ≤ R)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) :
    64 ≤ ⌈Real.log (2 * Real.exp 1 * R)⌉₊ := by
  have hL := rep_L_gt hR hq hqreg
  have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
  exact repnum_p_ge (by linarith) (by linarith)

/-- `log(2d') ≤ p` for every background dimension `1 ≤ d' ≤ 2R` (as `4 ≤ 2e`). -/
theorem rep_log_le_p {R d' : ℕ} (hR : 2 ≤ R) (hd1 : 1 ≤ d') (hd' : d' ≤ 2 * R) :
    Real.log (2 * d') ≤ ⌈Real.log (2 * Real.exp 1 * R)⌉₊ := by
  have _hR2 : 2 ≤ R := hR
  have h1 : (1 : ℝ) ≤ d' := by exact_mod_cast hd1
  have h2 : (d' : ℝ) ≤ 2 * R := by exact_mod_cast hd'
  exact repnum_log_le_p h1 h2

/-- The exact rational certificate (R2): `E⋆ ≤ δ_cross t₀`, i.e.
`22 √(301/(150 ρ₀ K⋆) + 67/(64 ρ₀² C⋆²)) + 2900/K⋆ ≤ (249/10000)(11/48)`. -/
theorem estar_le :
    22 * Real.sqrt (301 / (150 * rho0 * kStarRep) + 67 / (64 * rho0 ^ 2 * cStarRep ^ 2)) +
        2900 / (kStarRep : ℝ) ≤ 249 / 10000 * t0 :=
  repnum_estar_lt.le

/-- The refined cross-Gram bound is at most `δ_cross t₀` for every head size `N ≤ min(R, b/16)`
and background dimension `d' ≤ 2R` (paper, lines 996–1023). -/
theorem rep_crossBound_le {R q b N d' : ℕ} (hR : 2 ≤ R)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) (hbq : kStarRep * R ≤ b * q)
    (hN : N ≤ R) (hNb : 16 * N ≤ b) (hd' : d' ≤ 2 * R) :
    crossBound N d' ⌈Real.log (2 * Real.exp 1 * R)⌉₊ b (q / 2) ≤ 249 / 10000 * t0 := by
  unfold crossBound
  exact repnum_crossBound_core hR hq hqreg hbq hN hNb hd' _ _ rfl rfl

/-- `e^{-s/2304} < δ_ret = 1/40000`. -/
theorem rep_exp_lt {R q : ℕ} (hR : 2 ≤ R)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) :
    Real.exp (-((q / 2 : ℕ) : ℝ) / 2304) < 1 / 40000 := by
  have hs := rep_s_gt hR hq hqreg
  apply repnum_exp_lt
  have hc : 8 * rho0 * cStarRep ≤ 500000 := by
    unfold rho0 cStarRep
    norm_num
  linarith

/-- Group-2 union bound: `R · 2^s (e^{-s/2304}/16)^{s/12} < δ_ret` (paper, lines 1064–1084). -/
theorem rep_retention2_lt {R q : ℕ} (hR : 2 ≤ R)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) :
    (R : ℝ) * ((2 : ℝ) ^ (q / 2) *
        (Real.exp (-((q / 2 : ℕ) : ℝ) / 2304) / 16) ^ (((q / 2 : ℕ) : ℝ) / 12)) < 1 / 40000 := by
  have hs := rep_s_gt hR hq hqreg
  have hsge := rep_s_ge hR hq hqreg
  have hL := rep_L_gt hR hq hqreg
  have hqgt := rep_q_gt hR hq hqreg
  have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hR0 : (0 : ℝ) < R := by linarith
  -- (R8): the subset-bound exponent
  have hl2 := Real.log_two_lt_d9
  norm_num at hl2
  have hsub := repnum_subset_le (s := q / 2) (by linarith)
  -- (R7): `s² ≥ ρ₀² q² ≥ ρ₀² C⋆² L`
  have hL0 : 0 ≤ Real.log (Real.exp 1 * R) := by linarith
  have hq2 : cStarRep ^ 2 * Real.log (Real.exp 1 * R) ≤ (q : ℝ) ^ 2 := by
    have h0 : 0 ≤ cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) :=
      mul_nonneg repnum_cStar_pos.le (Real.sqrt_nonneg _)
    have h1 := pow_le_pow_left₀ h0 hq 2
    rw [mul_pow, Real.sq_sqrt hL0] at h1
    exact h1
  have hs2 : rho0 ^ 2 * cStarRep ^ 2 * Real.log (Real.exp 1 * R) ≤ ((q / 2 : ℕ) : ℝ) ^ 2 := by
    have h0 : 0 ≤ rho0 * q := mul_nonneg (by unfold rho0; norm_num) (by linarith)
    have h1 : (rho0 * q) ^ 2 ≤ ((q / 2 : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ h0 hsge 2
    have h2 := mul_le_mul_of_nonneg_left hq2 (sq_nonneg rho0)
    nlinarith
  have hun := repnum_union_lt hR0 (by linarith) hs2
  calc (R : ℝ) * ((2 : ℝ) ^ (q / 2) *
        (Real.exp (-((q / 2 : ℕ) : ℝ) / 2304) / 16) ^ (((q / 2 : ℕ) : ℝ) / 12))
      ≤ (R : ℝ) * Real.exp (-(((q / 2 : ℕ) : ℝ) ^ 2) / 55296) :=
        mul_le_mul_of_nonneg_left hsub hR0.le
    _ < 1 / 40000 := hun

end SparseStack
