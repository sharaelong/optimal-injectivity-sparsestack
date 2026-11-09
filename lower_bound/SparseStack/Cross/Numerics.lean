import SparseStack.Cross.Defs

/-!
# Cross-Gram bound: numerics (W-CROSS)

* `c_b < 19/12` (from `(1-1/b)^b ≤ e⁻¹` and `e > 19/7`), hence `c_b ≤ 2` and `2 c_b √46 ≤ 22`.
* `B = ⌊2b/s⌋ ≥ 3b/(2s)` when `b ≥ 2s`.
* `final_combine`: the closing real-arithmetic step (triangle inequality output →
  eq. (refined-cross)).
-/

namespace SparseStack
namespace Cross

open SparseFock SparseFock.SparseIIDCoupling

/-- `c_b > 0`. -/
theorem cB_pos {b : ℕ} (hb : 0 < b) : 0 < cB b :=
  lt_of_lt_of_le zero_lt_one (one_le_cB hb)

/-- `c_b < 19/12`. -/
theorem cB_lt_19_div_12 {b : ℕ} (hb : 0 < b) : cB b < 19 / 12 := by
  have hp := p0_le_exp_neg_one hb
  have he : Real.exp (-1) < 7 / 19 := by
    rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9
    linarith
  have h1 : (12 : ℝ) / 19 < 1 - p0 b := by linarith
  have h0 : (0 : ℝ) < 1 - p0 b := by linarith
  rw [cB, inv_eq_one_div, div_lt_div_iff₀ h0 (by norm_num)]
  linarith

/-- `c_b ≤ 2`. -/
theorem cB_le_two {b : ℕ} (hb : 0 < b) : cB b ≤ 2 := by
  linarith [cB_lt_19_div_12 hb]

/-- `2 c_b √46 ≤ 22`. -/
theorem two_mul_cB_mul_sqrt_46_le {b : ℕ} (hb : 0 < b) : 2 * cB b * Real.sqrt 46 ≤ 22 := by
  have h1 := cB_lt_19_div_12 hb
  have h0 := cB_pos hb
  have hs : Real.sqrt 46 ≤ 132 / 19 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs0 := Real.sqrt_nonneg 46
  nlinarith

/-- `B = ⌊2b/s⌋ ≥ 3b/(2s)` when `b ≥ 2s`. -/
theorem div_floor_ge {s b : ℕ} (hs : 1 ≤ s) (hbs : 2 * s ≤ b) :
    (3 * b : ℝ) / (2 * s) ≤ ((2 * b / s : ℕ) : ℝ) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hdm := Nat.div_add_mod (2 * b) s
  have hmod := Nat.mod_lt (2 * b) (by omega : s > 0)
  have hdmR : (s : ℝ) * ((2 * b / s : ℕ) : ℝ) + ((2 * b % s : ℕ) : ℝ) = 2 * b := by
    exact_mod_cast hdm
  have hmodR : ((2 * b % s : ℕ) : ℝ) < s := by exact_mod_cast hmod
  have hbsR : (2 : ℝ) * s ≤ b := by exact_mod_cast hbs
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The closing arithmetic: from `E‖H̃ᵀỸ‖ ≤ c (s⁻¹ (2 L + H))` with
`L ≤ √(46 (a + D_p/B + p))` and `H ≤ √(N d · 3 C(s,3)/b³)` to eq. (refined-cross). -/
theorem final_combine {c N d s b B a p C L H : ℝ} (hs : 1 ≤ s) (hb : 0 < b)
    (hB : 3 * b / (2 * s) ≤ B) (ha : a ≤ N / B + 1) (hN : 0 ≤ N) (hd : 0 ≤ d) (hp : 0 ≤ p)
    (hc0 : 0 ≤ c) (hc2 : c ≤ 2) (hc : 2 * c * Real.sqrt 46 ≤ 22)
    (hL : L ≤ Real.sqrt (46 * (a + (d + 2 * p + 1) / B + p)))
    (hH : H ≤ Real.sqrt (N * d * (3 * C / b ^ 3))) :
    c * (s⁻¹ * (2 * L + H)) ≤
      22 * Real.sqrt (2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2) +
        2 * Real.sqrt (3 * N * d / (s ^ 2 * b ^ 3) * C) := by
  have hs0 : 0 < s := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  have hK0 : 0 ≤ N + (d + 2 * p + 1) := by positivity
  -- `1/B ≤ 2s/(3b)`
  have hinvB : 1 / B ≤ 2 * s / (3 * b) := by
    rw [div_le_div_iff₀ hB0 (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hB
    linarith
  -- the argument of the first square root is at most `s² W`
  have hX : a + (d + 2 * p + 1) / B + p ≤
      s ^ 2 * (2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2) := by
    have h1 : a + (d + 2 * p + 1) / B + p ≤ (N + (d + 2 * p + 1)) / B + (p + 1) := by
      rw [add_div N]
      linarith
    have h2 : (N + (d + 2 * p + 1)) / B ≤ (N + (d + 2 * p + 1)) * (2 * s / (3 * b)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinvB hK0
    have h3 : s ^ 2 * (2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2) =
        (N + (d + 2 * p + 1)) * (2 * s / (3 * b)) + (p + 1) := by
      field_simp
    linarith
  have hLb : L ≤ s * Real.sqrt 46 *
      Real.sqrt (2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2) := by
    calc L ≤ Real.sqrt (46 * (a + (d + 2 * p + 1) / B + p)) := hL
      _ ≤ Real.sqrt (46 * (s ^ 2 *
            (2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2))) :=
          Real.sqrt_le_sqrt (by linarith)
      _ = s * Real.sqrt 46 *
            Real.sqrt (2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by positivity), Real.sqrt_sq hs0.le]
          ring
  have hHb : c * H ≤ 2 * Real.sqrt (N * d * (3 * C / b ^ 3)) :=
    calc c * H ≤ c * Real.sqrt (N * d * (3 * C / b ^ 3)) := mul_le_mul_of_nonneg_left hH hc0
      _ ≤ 2 * Real.sqrt (N * d * (3 * C / b ^ 3)) :=
          mul_le_mul_of_nonneg_right hc2 (Real.sqrt_nonneg _)
  have hsq2 : Real.sqrt (3 * N * d / (s ^ 2 * b ^ 3) * C) =
      Real.sqrt (N * d * (3 * C / b ^ 3)) / s := by
    have e : 3 * N * d / (s ^ 2 * b ^ 3) * C = N * d * (3 * C / b ^ 3) / s ^ 2 := by
      field_simp
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hs0.le]
  have hW0 := Real.sqrt_nonneg (2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2)
  have hcL : 2 * c * L ≤ 2 * c * (s * Real.sqrt 46 *
      Real.sqrt (2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2)) :=
    mul_le_mul_of_nonneg_left hLb (by positivity)
  have h22 : 2 * c * (s * Real.sqrt 46 *
      Real.sqrt (2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2)) ≤
      22 * Real.sqrt (2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2) * s := by
    have := mul_le_mul_of_nonneg_right hc (mul_nonneg hs0.le hW0)
    linarith
  have hmain : c * (s⁻¹ * (2 * L + H)) = (2 * c * L + c * H) / s := by
    field_simp
  rw [hmain, hsq2, div_le_iff₀ hs0]
  have e2 : (22 * Real.sqrt (2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2) +
      2 * (Real.sqrt (N * d * (3 * C / b ^ 3)) / s)) * s =
      22 * Real.sqrt (2 * (N + (d + 2 * p + 1)) / (3 * b * s) + (p + 1) / s ^ 2) * s +
        2 * Real.sqrt (N * d * (3 * C / b ^ 3)) := by
    field_simp
  rw [e2]
  linarith

end Cross
end SparseStack
