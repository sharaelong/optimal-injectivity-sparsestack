import SparseStack.Numerics.Params

/-!
# Numerical certificates for `thm:head-repair`, regime `q < H_rep L_R` (paper, lines 977–1110)

Constants (thm:main choices): `ρ₀ = 499/1000` (`rho0`), `H_rep = 256`, `a₀ = 11/12` (`a0`),
`t₀ = 11/48` (`t0`), `δ_cross = 249/10000`, `δ_ret = 1/40000`, `C⋆ = 255232512/15625` (`cStarRep`),
`K⋆ = 79840000` (`kStarRep`), `L_R = log(eR)`, `p = ⌈log(2eR)⌉`, `s = ⌊q/2⌋`.

General (real-variable) facts; instantiate `R` with `(R : ℝ)` for `R : ℕ`.
* (R1) `repnum_estar_lt_57`, `repnum_estar_lt`: `E⋆ < 57/10000 < δ_cross t₀` (rational, after
  isolating the square root);
* regime `C⋆ √L ≤ q < 256 L`: `repnum_regime_sqrt` (`√L > C⋆/256`), `repnum_regime_L_gt`
  (`L > 4071`), `repnum_regime_q_gt` (`q > 1040000`);
* (R2) `repnum_R_ge_300` (`R = e^{L-1} ≥ (L-1)³/6 ≥ 300 L` for `L ≥ 64`);
  (R3) `repnum_L_sq_le` (`L² ≤ 2R`), `repnum_L_cube_le` (`L³ ≤ 4R`), for `R ≥ 1`;
* (R4) `repnum_p_ge`, `repnum_p_succ_le`, `repnum_log_le_p`; (R5) `repnum_ND_le`;
* (R6) `repnum_exp_lt`; (R7) `repnum_union_lt`; (R8) `repnum_subset_le`;
* the refined cross-Gram budget: `repnum_first_term_le`, `repnum_remainder_le`,
  `repnum_crossBound_core` (the right-hand side of eq. (refined-cross) is `≤ δ_cross t₀`);
* (R9) `repnum_Hrep_rpow`, `repnum_remainder_const`; (R10) `repnum_ratio_gt`;
  (R11) `repnum_failure_sum`, `repnum_beta_eq`, `repnum_beta_lt`.
-/

namespace SparseStack

/-! ## Constants -/

theorem repnum_kStar_real : (kStarRep : ℝ) = 79840000 := by
  norm_num [kStarRep]

theorem repnum_cStar_pos : (0 : ℝ) < cStarRep := by
  unfold cStarRep
  norm_num

/-! ## Elementary exponential bounds -/

/-- `e^{11} > 40000`. -/
theorem repnum_exp_eleven_gt : (40000 : ℝ) < Real.exp 11 := by
  have he := Real.exp_one_gt_d9
  have h11 : Real.exp 11 = Real.exp 1 ^ 11 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h11]
  calc (40000 : ℝ) < 2.7182818283 ^ 11 := by norm_num
    _ < Real.exp 1 ^ 11 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)

/-- `e^{-11} < 1/40000`. -/
theorem repnum_exp_neg_eleven_lt : Real.exp (-11) < 1 / 40000 := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) repnum_exp_eleven_gt

/-! ## (R1) The cross budget `E⋆ < δ_cross t₀` -/

/-- (R1) `E⋆ = 22 √(301/(150 ρ₀ K⋆) + 67/(64 ρ₀² C⋆²)) + 2900/K⋆ < 57/10000`. -/
theorem repnum_estar_lt_57 :
    22 * Real.sqrt (301 / (150 * rho0 * kStarRep) + 67 / (64 * rho0 ^ 2 * cStarRep ^ 2)) +
        2900 / (kStarRep : ℝ) < 57 / 10000 := by
  have hS : Real.sqrt (301 / (150 * rho0 * kStarRep) + 67 / (64 * rho0 ^ 2 * cStarRep ^ 2)) <
      (57 / 10000 - 2900 / 79840000) / 22 := by
    rw [Real.sqrt_lt' (by norm_num), repnum_kStar_real]
    unfold rho0 cStarRep
    norm_num
  rw [repnum_kStar_real] at hS ⊢
  linarith

/-- (R1) `E⋆ < δ_cross t₀ = (249/10000)(11/48)`. -/
theorem repnum_estar_lt :
    22 * Real.sqrt (301 / (150 * rho0 * kStarRep) + 67 / (64 * rho0 ^ 2 * cStarRep ^ 2)) +
        2900 / (kStarRep : ℝ) < 249 / 10000 * t0 := by
  have h := repnum_estar_lt_57
  unfold t0
  linarith

/-! ## The regime `C⋆ √L ≤ q < 256 L` -/

/-- In the regime `C⋆ √L ≤ q < 256 L`: `C⋆/256 < √L`. -/
theorem repnum_regime_sqrt {L q : ℝ} (hq : cStarRep * Real.sqrt L ≤ q) (hqreg : q < 256 * L) :
    cStarRep / 256 < Real.sqrt L := by
  have hC := repnum_cStar_pos
  have hL0 : 0 < L := by
    have : 0 ≤ cStarRep * Real.sqrt L := mul_nonneg hC.le (Real.sqrt_nonneg _)
    linarith
  have hs0 : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hss : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have h1 : cStarRep * Real.sqrt L < (256 * Real.sqrt L) * Real.sqrt L := by nlinarith
  have h2 : cStarRep < 256 * Real.sqrt L := lt_of_mul_lt_mul_right h1 hs0.le
  linarith

/-- In the regime `C⋆ √L ≤ q < 256 L`: `L > 4071` (as `(C⋆/256)² > 4071.2`). -/
theorem repnum_regime_L_gt {L q : ℝ} (hq : cStarRep * Real.sqrt L ≤ q) (hqreg : q < 256 * L) :
    4071 < L := by
  have h := repnum_regime_sqrt hq hqreg
  have hc : (63.806 : ℝ) < cStarRep / 256 := by
    unfold cStarRep
    norm_num
  have hs : (63.806 : ℝ) < Real.sqrt L := lt_trans hc h
  have hL0 : 0 < L := Real.sqrt_pos.mp (lt_trans (by norm_num) hs)
  have hss : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  nlinarith

/-- In the regime `C⋆ √L ≤ q < 256 L`: `q > 1040000` (as `C⋆²/256 > 1042298`). -/
theorem repnum_regime_q_gt {L q : ℝ} (hq : cStarRep * Real.sqrt L ≤ q) (hqreg : q < 256 * L) :
    1040000 < q := by
  have h := repnum_regime_sqrt hq hqreg
  have hC := repnum_cStar_pos
  have h1 : cStarRep * (cStarRep / 256) < cStarRep * Real.sqrt L := mul_lt_mul_of_pos_left h hC
  have h2 : (1040000 : ℝ) < cStarRep * (cStarRep / 256) := by
    unfold cStarRep
    norm_num
  linarith

/-! ## (R2), (R3) Size of `R = e^{L-1}` -/

/-- `log(eR) = 1 + log R`. -/
theorem repnum_logER_eq {R : ℝ} (hR : 0 < R) : Real.log (Real.exp 1 * R) = 1 + Real.log R := by
  rw [Real.log_mul (Real.exp_pos 1).ne' hR.ne', Real.log_exp]

/-- `R = e^{L-1}`. -/
theorem repnum_R_eq_exp {R : ℝ} (hR : 0 < R) : R = Real.exp (Real.log (Real.exp 1 * R) - 1) := by
  rw [repnum_logER_eq hR, add_sub_cancel_left, Real.exp_log hR]

/-- (R2) `R = e^{L-1} ≥ 300 L` once `L = log(eR) ≥ 64` (via `e^x ≥ x³/6`). -/
theorem repnum_R_ge_300 {R : ℝ} (hR : 0 < R) (hL : 64 ≤ Real.log (Real.exp 1 * R)) :
    300 * Real.log (Real.exp 1 * R) ≤ R := by
  have hRe := repnum_R_eq_exp hR
  set L := Real.log (Real.exp 1 * R) with hLdef
  have hx : 0 ≤ L - 1 := by linarith
  have h3 := Real.pow_div_factorial_le_exp _ hx 3
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at h3
  have hy : 0 ≤ L - 64 := by linarith
  rw [hRe]
  nlinarith [mul_nonneg (mul_nonneg hy hy) hy, mul_nonneg hy hy]

/-- (R3) `L² ≤ 2R` for `R ≥ 1` (via `e^x ≥ 1 + x + x²/2`). -/
theorem repnum_L_sq_le {R : ℝ} (hR : 1 ≤ R) : Real.log (Real.exp 1 * R) ^ 2 ≤ 2 * R := by
  have hR0 : 0 < R := by linarith
  have hRe := repnum_R_eq_exp hR0
  have hL1 : 1 ≤ Real.log (Real.exp 1 * R) := by
    rw [repnum_logER_eq hR0]
    have := Real.log_nonneg hR
    linarith
  set L := Real.log (Real.exp 1 * R) with hLdef
  have hx : 0 ≤ L - 1 := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg hx
  rw [hRe]
  nlinarith

/-- (R3) `L³ ≤ 4R` for `R ≥ 1` (via `e^x ≥ ∑_{k ≤ 4} x^k/k!` and an explicit SOS). -/
theorem repnum_L_cube_le {R : ℝ} (hR : 1 ≤ R) : Real.log (Real.exp 1 * R) ^ 3 ≤ 4 * R := by
  have hR0 : 0 < R := by linarith
  have hRe := repnum_R_eq_exp hR0
  have hL1 : 1 ≤ Real.log (Real.exp 1 * R) := by
    rw [repnum_logER_eq hR0]
    have := Real.log_nonneg hR
    linarith
  set L := Real.log (Real.exp 1 * R) with hLdef
  have hx : 0 ≤ L - 1 := by linarith
  have h5 := Real.sum_le_exp_of_nonneg hx 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h5
  norm_num [Nat.factorial] at h5
  rw [hRe]
  nlinarith [sq_nonneg ((L - 1) ^ 2 - (L - 1) - 15 / 4), sq_nonneg ((L - 1) - 3 / 2)]

/-! ## (R4), (R5) The moment order `p = ⌈log(2eR)⌉` -/

/-- `log(2eR) = log 2 + log(eR)`. -/
theorem repnum_log2eR_eq {R : ℝ} (hR : 0 < R) :
    Real.log (2 * Real.exp 1 * R) = Real.log 2 + Real.log (Real.exp 1 * R) := by
  rw [mul_assoc, Real.log_mul (by norm_num) (by positivity)]

/-- (R4) `p = ⌈log(2eR)⌉ ≥ 64` once `L ≥ 64`. -/
theorem repnum_p_ge {R : ℝ} (hR : 0 < R) (hL : 64 ≤ Real.log (Real.exp 1 * R)) :
    64 ≤ ⌈Real.log (2 * Real.exp 1 * R)⌉₊ := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : ((63 : ℕ) : ℝ) < Real.log (2 * Real.exp 1 * R) := by
    rw [repnum_log2eR_eq hR]
    push_cast
    linarith
  have := Nat.lt_ceil.mpr h
  omega

/-- (R4) `p + 1 ≤ (67/64) L` once `L ≥ 64`. -/
theorem repnum_p_succ_le {R : ℝ} (hR : 0 < R) (hL : 64 ≤ Real.log (Real.exp 1 * R)) :
    (⌈Real.log (2 * Real.exp 1 * R)⌉₊ : ℝ) + 1 ≤ 67 / 64 * Real.log (Real.exp 1 * R) := by
  have h2 := Real.log_two_lt_d9
  have h2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : 0 ≤ Real.log (2 * Real.exp 1 * R) := by
    rw [repnum_log2eR_eq hR]
    linarith
  have hc := Nat.ceil_lt_add_one hnn
  have heq := repnum_log2eR_eq hR
  norm_num at h2
  linarith

/-- (R4) `log(2d) ≤ p` for `1 ≤ d ≤ 2R` (as `4R ≤ 2eR`). -/
theorem repnum_log_le_p {R d : ℝ} (hd : 1 ≤ d) (hdR : d ≤ 2 * R) :
    Real.log (2 * d) ≤ ⌈Real.log (2 * Real.exp 1 * R)⌉₊ := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1
    linarith
  have hR : 0 < R := by linarith
  have h1 : 2 * d ≤ 2 * Real.exp 1 * R := by nlinarith
  calc Real.log (2 * d) ≤ Real.log (2 * Real.exp 1 * R) := Real.log_le_log (by linarith) h1
    _ ≤ ⌈Real.log (2 * Real.exp 1 * R)⌉₊ := Nat.le_ceil _

/-- (R5) `N + D_p = N + (d + 2p + 1) ≤ (301/100) R` for `N ≤ R`, `d ≤ 2R`, `L ≥ 64`. -/
theorem repnum_ND_le {R N d : ℝ} (hR : 0 < R) (hL : 64 ≤ Real.log (Real.exp 1 * R))
    (hN : N ≤ R) (hd : d ≤ 2 * R) :
    N + (d + 2 * (⌈Real.log (2 * Real.exp 1 * R)⌉₊ : ℝ) + 1) ≤ 301 / 100 * R := by
  have hp := repnum_p_succ_le hR hL
  have h300 := repnum_R_ge_300 hR hL
  linarith

/-! ## (R6)–(R8) Retention bounds -/

/-- (R6) `s ≥ 8 ρ₀ C⋆ ⇒ e^{-s/2304} < δ_ret = 1/40000`. -/
theorem repnum_exp_lt {s : ℝ} (hs : 8 * rho0 * cStarRep ≤ s) :
    Real.exp (-s / 2304) < 1 / 40000 := by
  have hc : (25344 : ℝ) ≤ 8 * rho0 * cStarRep := by
    unfold rho0 cStarRep
    norm_num
  have h1 : -s / 2304 ≤ -11 := by linarith
  calc Real.exp (-s / 2304) ≤ Real.exp (-11) := Real.exp_le_exp.mpr h1
    _ < 1 / 40000 := repnum_exp_neg_eleven_lt

/-- (R7) `s² ≥ ρ₀² C⋆² L`, `L ≥ 64 ⇒ R e^{-s²/55296} < δ_ret` (as `ρ₀² C⋆²/55296 ≥ 37/32` and
`R = e^{L-1}`). -/
theorem repnum_union_lt {R s : ℝ} (hR : 0 < R) (hL : 64 ≤ Real.log (Real.exp 1 * R))
    (hs : rho0 ^ 2 * cStarRep ^ 2 * Real.log (Real.exp 1 * R) ≤ s ^ 2) :
    R * Real.exp (-(s ^ 2) / 55296) < 1 / 40000 := by
  have hRe := repnum_R_eq_exp hR
  set L := Real.log (Real.exp 1 * R) with hLdef
  have hc : (37 / 32 : ℝ) * 55296 ≤ rho0 ^ 2 * cStarRep ^ 2 := by
    unfold rho0 cStarRep
    norm_num
  have hcL := mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ L)
  have h1 : -(s ^ 2) / 55296 ≤ -(37 / 32) * L := by linarith
  calc R * Real.exp (-(s ^ 2) / 55296)
      = Real.exp (L - 1) * Real.exp (-(s ^ 2) / 55296) := by rw [← hRe]
    _ = Real.exp (L - 1 + -(s ^ 2) / 55296) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-11) := Real.exp_le_exp.mpr (by linarith)
    _ < 1 / 40000 := repnum_exp_neg_eleven_lt

/-- (R8) subset-bound exponent: for `s ≥ 36864 log 2`,
`2^s (e^{-s/2304}/16)^{s/12} = exp((2/3) s log 2 - s²/27648) ≤ e^{-s²/55296}`. -/
theorem repnum_subset_le {s : ℕ} (hs : 36864 * Real.log 2 ≤ s) :
    (2 : ℝ) ^ s * (Real.exp (-(s : ℝ) / 2304) / 16) ^ ((s : ℝ) / 12) ≤
      Real.exp (-((s : ℝ) ^ 2) / 55296) := by
  have hpos : 0 < Real.exp (-(s : ℝ) / 2304) / 16 := by positivity
  have hlog : Real.log (Real.exp (-(s : ℝ) / 2304) / 16) = -(s : ℝ) / 2304 - 4 * Real.log 2 := by
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp,
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  have h2s : (2 : ℝ) ^ s = Real.exp (s * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [h2s, Real.rpow_def_of_pos hpos, hlog, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  nlinarith [mul_le_mul_of_nonneg_left hs hs0]

/-! ## The refined cross-Gram budget (paper, lines 996–1023) -/

/-- First term of eq. (refined-cross): `2(N + D_p)/(3bs) + (p+1)/s² ≤ S⋆`, using `b s ≥ ρ₀ b q ≥
ρ₀ K⋆ R`, `N + D_p ≤ (301/100) R`, `p + 1 ≤ (67/64) L` and `s² ≥ ρ₀² q² ≥ ρ₀² C⋆² L`. -/
theorem repnum_first_term_le {R q b s L N d p : ℝ} (hb : 0 < b) (hs0 : 0 < s)
    (hsq : rho0 * q ≤ s) (hq0 : 0 ≤ q) (hbq : (kStarRep : ℝ) * R ≤ b * q)
    (hq2 : cStarRep ^ 2 * L ≤ q ^ 2) (hND : N + (d + 2 * p + 1) ≤ 301 / 100 * R)
    (hpL : p + 1 ≤ 67 / 64 * L) :
    2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2 ≤
      301 / (150 * rho0 * kStarRep) + 67 / (64 * rho0 ^ 2 * cStarRep ^ 2) := by
  have hC := repnum_cStar_pos
  have h1 : 2 * (N + (d + 2 * p + 1)) / (3 * b * s) ≤ 301 / (150 * rho0 * kStarRep) := by
    rw [repnum_kStar_real]
    rw [div_le_div_iff₀ (by positivity) (by unfold rho0; norm_num)]
    have hbs : b * (rho0 * q) ≤ b * s := mul_le_mul_of_nonneg_left hsq hb.le
    rw [repnum_kStar_real] at hbq
    unfold rho0 at hbs ⊢
    nlinarith
  have h2 : (p + 1) / s ^ 2 ≤ 67 / (64 * rho0 ^ 2 * cStarRep ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by unfold rho0; positivity)]
    have hρq : 0 ≤ rho0 * q := mul_nonneg (by unfold rho0; norm_num) hq0
    have hss : (rho0 * q) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hρq hsq 2
    have hc2 : 0 ≤ rho0 ^ 2 * cStarRep ^ 2 := by positivity
    have e1 := mul_le_mul_of_nonneg_left hpL (by positivity : (0 : ℝ) ≤ 64 * rho0 ^ 2 * cStarRep ^ 2)
    have e2 := mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ rho0 ^ 2)
    nlinarith
  linarith

/-- Remainder term of eq. (refined-cross): `2 √(3Nd/(s²b³) · C(s,3)) ≤ 2900/K⋆`, using
`C(s,3) ≤ s³/6`, `N ≤ b/16`, `d ≤ 2R`, `s ≤ q/2`, `K⋆ R ≤ b q`, `q < 256 L`, `L³ ≤ 4R`
(paper: `≤ √(Rs)/(2b) ≤ H_rep^{3/2}/(√2 K⋆) < 2900/K⋆`). -/
theorem repnum_remainder_le {R q b s L N d c3 : ℝ} (hR : 0 < R) (hb : 0 < b) (hs0 : 0 < s)
    (hq0 : 0 < q) (hN0 : 0 ≤ N) (hd0 : 0 ≤ d) (hc3le : c3 ≤ s ^ 3 / 6)
    (hs2 : s ≤ q / 2) (hbq : (kStarRep : ℝ) * R ≤ b * q) (hqreg : q < 256 * L)
    (hL3 : L ^ 3 ≤ 4 * R) (hNb : 16 * N ≤ b) (hd : d ≤ 2 * R) :
    2 * Real.sqrt (3 * N * d / (s ^ 2 * b ^ 3) * c3) ≤ 2900 / kStarRep := by
  rw [repnum_kStar_real] at hbq ⊢
  -- `X ≤ N d s/(2 b³) ≤ R s/(16 b²) ≤ (1450/K⋆)²`
  have hX1 : 3 * N * d / (s ^ 2 * b ^ 3) * c3 ≤ N * d * s / (2 * b ^ 3) := by
    have hA : 0 ≤ 3 * N * d / (s ^ 2 * b ^ 3) := by positivity
    calc 3 * N * d / (s ^ 2 * b ^ 3) * c3 ≤ 3 * N * d / (s ^ 2 * b ^ 3) * (s ^ 3 / 6) :=
          mul_le_mul_of_nonneg_left hc3le hA
      _ = N * d * s / (2 * b ^ 3) := by
          field_simp
          ring
  have hX2 : N * d * s / (2 * b ^ 3) ≤ R * s / (16 * b ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hNd : N * d ≤ b / 16 * (2 * R) :=
      mul_le_mul (by linarith) hd hd0 (by positivity)
    have e1 := mul_le_mul_of_nonneg_right hNd (by positivity : (0 : ℝ) ≤ s * (16 * b ^ 2))
    nlinarith
  have hX3 : R * s / (16 * b ^ 2) ≤ (1450 / 79840000) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    -- `R² s K⋆² ≤ b² q² s ≤ b² q³/2 < b² (256 L)³/2 ≤ 2·256³ b² R`
    have hKR : (79840000 * R) ^ 2 ≤ (b * q) ^ 2 := pow_le_pow_left₀ (by positivity) hbq 2
    have hq3 : q ^ 3 < (256 * L) ^ 3 := pow_lt_pow_left₀ hqreg hq0.le (by norm_num)
    have hqs : q ^ 2 * s ≤ q ^ 2 * (q / 2) := mul_le_mul_of_nonneg_left hs2 (by positivity)
    have e1 : (79840000 * R) ^ 2 * s ≤ (b * q) ^ 2 * s := mul_le_mul_of_nonneg_right hKR hs0.le
    have e2 : b ^ 2 * (q ^ 2 * s) ≤ b ^ 2 * (q ^ 2 * (q / 2)) :=
      mul_le_mul_of_nonneg_left hqs (by positivity)
    have e3 : b ^ 2 * q ^ 3 ≤ b ^ 2 * ((256 * L) ^ 3) :=
      mul_le_mul_of_nonneg_left hq3.le (by positivity)
    have e4 : b ^ 2 * L ^ 3 ≤ b ^ 2 * (4 * R) := mul_le_mul_of_nonneg_left hL3 (by positivity)
    -- `R (R s K⋆²) ≤ R (33554432 b²)`
    have key : R * (R * s * 79840000 ^ 2) ≤ R * (33554432 * b ^ 2) := by nlinarith
    have key2 : R * s * 79840000 ^ 2 ≤ 33554432 * b ^ 2 := le_of_mul_le_mul_left key hR
    nlinarith
  have hX : 3 * N * d / (s ^ 2 * b ^ 3) * c3 ≤ (1450 / 79840000) ^ 2 :=
    le_trans hX1 (le_trans hX2 hX3)
  have hsq : Real.sqrt (3 * N * d / (s ^ 2 * b ^ 3) * c3) ≤ 1450 / 79840000 := by
    calc Real.sqrt (3 * N * d / (s ^ 2 * b ^ 3) * c3) ≤ Real.sqrt ((1450 / 79840000) ^ 2) :=
          Real.sqrt_le_sqrt hX
      _ = 1450 / 79840000 := Real.sqrt_sq (by norm_num)
  linarith

/-- The refined cross-Gram bound (the right-hand side of eq. (refined-cross), with `p, s` free
but pinned by `hp`, `hs`) is at most `δ_cross t₀`, in the regime of `head_repair`
(paper, lines 996–1023). -/
theorem repnum_crossBound_core {R q b N d : ℕ} (hR : 2 ≤ R)
    (hq : cStarRep * Real.sqrt (Real.log (Real.exp 1 * R)) ≤ q)
    (hqreg : (q : ℝ) < 256 * Real.log (Real.exp 1 * R)) (hbq : kStarRep * R ≤ b * q)
    (hN : N ≤ R) (hNb : 16 * N ≤ b) (hd : d ≤ 2 * R) (p s : ℕ)
    (hp : p = ⌈Real.log (2 * Real.exp 1 * R)⌉₊) (hs : s = q / 2) :
    22 * Real.sqrt (2 * ((N : ℝ) + ((d : ℝ) + 2 * p + 1)) / (3 * b * s) +
        ((p : ℝ) + 1) / (s : ℝ) ^ 2) +
      2 * Real.sqrt (3 * (N : ℝ) * d / ((s : ℝ) ^ 2 * (b : ℝ) ^ 3) * (Nat.choose s 3 : ℝ)) ≤
      249 / 10000 * t0 := by
  -- regime facts
  have hLgt := repnum_regime_L_gt hq hqreg
  have hqgt := repnum_regime_q_gt hq hqreg
  set L := Real.log (Real.exp 1 * R) with hLdef
  have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hR0 : (0 : ℝ) < R := by linarith
  have hL64 : 64 ≤ L := by linarith
  -- `s = ⌊q/2⌋`: `ρ₀ q ≤ s ≤ q/2`, `s > 0`
  have hq500 : 500 ≤ q := by
    have : (500 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hsN : 499 * q ≤ 1000 * s := by omega
  have hsqR : rho0 * q ≤ s := by
    have : (499 : ℝ) * q ≤ 1000 * s := by exact_mod_cast hsN
    unfold rho0
    linarith
  have hs2 : (s : ℝ) ≤ q / 2 := by
    rw [hs]
    exact Nat.cast_div_le
  have hs0 : (0 : ℝ) < s := by
    have : 0 < s := by omega
    exact_mod_cast this
  have hq0 : (0 : ℝ) < q := by linarith
  -- `b > 0`
  have hbqR : (kStarRep : ℝ) * R ≤ b * q := by exact_mod_cast hbq
  have hb : (0 : ℝ) < b := by
    have hK : (0 : ℝ) < (kStarRep : ℝ) * R := by
      rw [repnum_kStar_real]
      positivity
    have hbq0 : (0 : ℝ) < b * q := lt_of_lt_of_le hK hbqR
    by_contra hcon
    have hb0 : (b : ℝ) ≤ 0 := not_lt.mp hcon
    have : (b : ℝ) * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb0 hq0.le
    linarith
  -- `C⋆² L ≤ q²`
  have hL0 : 0 ≤ L := by linarith
  have hq2 : cStarRep ^ 2 * L ≤ (q : ℝ) ^ 2 := by
    have h0 : 0 ≤ cStarRep * Real.sqrt L := mul_nonneg repnum_cStar_pos.le (Real.sqrt_nonneg _)
    have h1 : (cStarRep * Real.sqrt L) ^ 2 ≤ (q : ℝ) ^ 2 := pow_le_pow_left₀ h0 hq 2
    rw [mul_pow, Real.sq_sqrt hL0] at h1
    exact h1
  -- `p + 1 ≤ (67/64) L`, `N + D_p ≤ (301/100) R`, `L³ ≤ 4R`
  have hpL : (p : ℝ) + 1 ≤ 67 / 64 * L := by
    rw [hp]
    exact repnum_p_succ_le hR0 hL64
  have hNR : (N : ℝ) ≤ R := by exact_mod_cast hN
  have hdR : (d : ℝ) ≤ 2 * R := by exact_mod_cast hd
  have hND : (N : ℝ) + ((d : ℝ) + 2 * p + 1) ≤ 301 / 100 * R := by
    rw [hp]
    exact repnum_ND_le hR0 hL64 hNR hdR
  have hL3 : L ^ 3 ≤ 4 * R := repnum_L_cube_le (by linarith)
  -- the two terms
  have hfirst := repnum_first_term_le hb hs0 hsqR hq0.le hbqR hq2 hND hpL
  have hc3 : (Nat.choose s 3 : ℝ) ≤ (s : ℝ) ^ 3 / 6 := by
    have := Nat.choose_le_pow_div (α := ℝ) 3 s
    norm_num [Nat.factorial] at this
    exact this
  have hNbR : 16 * (N : ℝ) ≤ b := by exact_mod_cast hNb
  have hrem := repnum_remainder_le hR0 hb hs0 hq0 (Nat.cast_nonneg N) (Nat.cast_nonneg d)
    hc3 hs2 hbqR hqreg hL3 hNbR hdR
  have hsqrt : Real.sqrt (2 * ((N : ℝ) + ((d : ℝ) + 2 * p + 1)) / (3 * b * s) +
      ((p : ℝ) + 1) / (s : ℝ) ^ 2) ≤
      Real.sqrt (301 / (150 * rho0 * kStarRep) + 67 / (64 * rho0 ^ 2 * cStarRep ^ 2)) :=
    Real.sqrt_le_sqrt hfirst
  have hE := repnum_estar_lt
  linarith

/-! ## (R9)–(R11) Remaining constants -/

/-- `H_rep^{3/2} = 256^{3/2} = 4096`. -/
theorem repnum_Hrep_rpow : (256 : ℝ) ^ ((3 : ℝ) / 2) = 4096 := by
  have h : (256 : ℝ) = 16 ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    norm_num
  rw [h, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16)]
  have h3 : (2 : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) := by norm_num
  rw [h3, Real.rpow_natCast]
  norm_num

/-- (R9) `H_rep^{3/2}/(√2 K⋆) < 2900/K⋆`. -/
theorem repnum_remainder_const :
    (256 : ℝ) ^ ((3 : ℝ) / 2) / (Real.sqrt 2 * kStarRep) < 2900 / kStarRep := by
  rw [repnum_Hrep_rpow, repnum_kStar_real]
  have h2 : (1.414 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- (R10) `K⋆/(2 H_rep²) > 2`. -/
theorem repnum_ratio_gt : (2 : ℝ) < (kStarRep : ℝ) / (2 * 256 ^ 2) := by
  rw [repnum_kStar_real]
  norm_num

/-- (R11) `2 δ_cross + 2 δ_ret = 997/20000`. -/
theorem repnum_failure_sum : 2 * (249 / 10000 : ℝ) + 2 * (1 / 40000) = 997 / 20000 := by
  norm_num

/-- (R11) `β = ρ₀ (a₀ - 2 t₀)`. -/
theorem repnum_beta_eq : rho0 * (a0 - 2 * t0) = betaRep := by
  unfold rho0 a0 t0 betaRep
  norm_num

/-- (R11) `β < 1/2`. -/
theorem repnum_beta_lt : betaRep < 1 / 2 := by
  unfold betaRep
  norm_num

end SparseStack
