import SparseStack.Basic.Defs

/-!
# Parameter facts for `ζ = numBlocks r`, `b = numBuckets r` (paper, `prop:parameters`, lines 1184–1185,
1332–1337, and thm:main's "In particular")

`L = log(e r) = 1 + log r`.

Proof plan (paper lines 1184–1185, 1332–1337, 1345–1361):
* `L = 1 + log r ≥ 1` and `L ≤ r` (from `log r ≤ r - 1`);
* `C √L ≤ ζ < C √L + 1` (ceiling), so `ζ ≥ C ≥ 2000` and, since `√L ≤ L ≤ r`, `ζ ≤ C r ≤ (C+1) r`;
* `b = ⌈K r/ζ⌉` gives `K r/ζ ≤ b < K r/ζ + 1`, i.e. `K r ≤ b ζ < K r + ζ`; and
  `K r/ζ ≥ K/(C+1) > 1` gives `b ≥ 2`;
* `K r + ζ ≤ (K + C + 1) r` from `ζ ≤ (C+1) r`;
* the constants `α`, `ρ₀/v (β/γ - u)` are exact rationals (`norm_num`).
-/

namespace SparseStack

/-- `L = log(e r)`. -/
noncomputable def logER (r : ℕ) : ℝ := Real.log (Real.exp 1 * (r : ℝ))

theorem logER_eq {r : ℕ} (hr : 1 ≤ r) : logER r = 1 + Real.log r := by
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    exact this.ne'
  unfold logER
  rw [Real.log_mul (Real.exp_pos 1).ne' hr0, Real.log_exp]

theorem one_le_logER {r : ℕ} (hr : 1 ≤ r) : 1 ≤ logER r := by
  rw [logER_eq hr]
  have : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  linarith

/-- `L ≤ r`. -/
theorem logER_le {r : ℕ} (hr : 1 ≤ r) : logER r ≤ r := by
  rw [logER_eq hr]
  have hpos : (0 : ℝ) < r := by exact_mod_cast hr
  have := Real.log_le_sub_one_of_pos hpos
  linarith

/-- `numBlocks r = ⌈C √L⌉`. -/
theorem numBlocks_eq_ceil (r : ℕ) :
    numBlocks r = Nat.ceil ((constC : ℝ) * Real.sqrt (logER r)) := rfl

/-- `C √L ≤ ζ`. -/
theorem numBlocks_ge (r : ℕ) : (constC : ℝ) * Real.sqrt (logER r) ≤ numBlocks r := by
  rw [numBlocks_eq_ceil]
  exact Nat.le_ceil _

/-- `ζ < C √L + 1`. -/
theorem numBlocks_lt {r : ℕ} (hr : 2 ≤ r) :
    (numBlocks r : ℝ) < (constC : ℝ) * Real.sqrt (logER r) + 1 := by
  have _h2 : 2 ≤ r := hr
  rw [numBlocks_eq_ceil]
  exact Nat.ceil_lt_add_one (by positivity)

/-- `(constC : ℝ) = 32768`. -/
theorem constC_real : (constC : ℝ) = 32768 := by
  norm_num [constC]

/-- `(constK : ℝ) = 160000000`. -/
theorem constK_real : (constK : ℝ) = 160000000 := by
  norm_num [constK]

/-- `ζ ≥ 2000` (indeed `ζ ≥ 42639`). -/
theorem numBlocks_ge_2000 {r : ℕ} (hr : 2 ≤ r) : 2000 ≤ numBlocks r := by
  have h1 : 1 ≤ logER r := one_le_logER (by omega)
  have hs : 1 ≤ Real.sqrt (logER r) := Real.one_le_sqrt.mpr h1
  have h2 := numBlocks_ge r
  rw [constC_real] at h2
  have : (2000 : ℝ) ≤ numBlocks r := by nlinarith
  exact_mod_cast this

/-- `0 < ζ` as a real number. -/
theorem numBlocks_pos_real {r : ℕ} (hr : 2 ≤ r) : (0 : ℝ) < numBlocks r := by
  have := numBlocks_ge_2000 hr
  have h : 0 < numBlocks r := by omega
  exact_mod_cast h

/-- `ζ ≤ (C+1) r`. -/
theorem numBlocks_le {r : ℕ} (hr : 2 ≤ r) : numBlocks r ≤ (constC + 1) * r := by
  have h1 : 1 ≤ logER r := one_le_logER (by omega)
  have hle : logER r ≤ r := logER_le (by omega)
  have hs : 1 ≤ Real.sqrt (logER r) := Real.one_le_sqrt.mpr h1
  have hss : Real.sqrt (logER r) * Real.sqrt (logER r) = logER r :=
    Real.mul_self_sqrt (by linarith)
  have hsq : Real.sqrt (logER r) ≤ logER r := by nlinarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  rw [numBlocks_eq_ceil]
  apply Nat.ceil_le.mpr
  push_cast
  rw [constC_real]
  nlinarith

/-- `b ≥ K r/ζ`, i.e. `b ζ ≥ K r`. -/
theorem numBuckets_mul_ge {r : ℕ} (hr : 2 ≤ r) : constK * r ≤ numBuckets r * numBlocks r := by
  have hz := numBlocks_pos_real hr
  have h : (constK : ℝ) * (r : ℝ) / (numBlocks r : ℝ) ≤ (numBuckets r : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hz] at h
  exact_mod_cast h

/-- `b ≥ 2`. -/
theorem two_le_numBuckets {r : ℕ} (hr : 2 ≤ r) : 2 ≤ numBuckets r := by
  have hz := numBlocks_pos_real hr
  have hle : (numBlocks r : ℝ) ≤ ((constC : ℝ) + 1) * r := by exact_mod_cast numBlocks_le hr
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hgt : (1 : ℝ) < (constK : ℝ) * r / numBlocks r := by
    rw [lt_div_iff₀ hz]
    rw [constC_real] at hle
    rw [constK_real]
    nlinarith
  have h1 : 1 < numBuckets r := Nat.lt_ceil.mpr (by exact_mod_cast hgt)
  omega

/-- `b ζ ≤ K r + ζ`. -/
theorem numBuckets_mul_le {r : ℕ} (hr : 2 ≤ r) :
    numBuckets r * numBlocks r ≤ constK * r + numBlocks r := by
  have hz := numBlocks_pos_real hr
  have h : (numBuckets r : ℝ) < (constK : ℝ) * (r : ℝ) / (numBlocks r : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h2 : (numBuckets r : ℝ) * numBlocks r < (constK : ℝ) * r + numBlocks r := by
    have := mul_lt_mul_of_pos_right h hz
    rwa [add_mul, div_mul_cancel₀ _ hz.ne', one_mul] at this
  have h3 : numBuckets r * numBlocks r < constK * r + numBlocks r := by exact_mod_cast h2
  omega

/-- `K r + ζ ≤ (K + C + 1) r`. -/
theorem size_le {r : ℕ} (hr : 2 ≤ r) : constK * r + numBlocks r ≤ (constK + constC + 1) * r := by
  have h := numBlocks_le hr
  calc constK * r + numBlocks r ≤ constK * r + (constC + 1) * r := Nat.add_le_add_left h _
    _ = (constK + constC + 1) * r := by ring

/-- `α > 10⁻⁴`. -/
theorem alpha_gt : (1 : ℝ) / 10000 < constAlpha := by
  unfold constAlpha
  norm_num

/-- `α = (ρ₀/v)(β/γ - u)` (the assembled margin, paper line 1360). -/
theorem alpha_eq_margin : constAlpha = rho0 / vCert * (betaRep / gammaRep - uCert) := by
  unfold constAlpha rho0 vCert betaRep gammaRep uCert
  norm_num

end SparseStack
