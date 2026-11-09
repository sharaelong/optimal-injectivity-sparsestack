import Mathlib

/-!
# Numerical conditions (L') of `thm:localization` for `ε = 1/3` (W-LOC)

`η = 1/96000`, `λ² = 121/45000`, `Θ = 48800`, `M = 440000` (paper, lines 376–393, 423–428).

* `lt_exp_57_div_4`: `16/η = 1536000 < e^{57/4}`, i.e. `log(16/η) < 57/4`
  (via `1536000⁴ < 2.718⁵⁷ < e⁵⁷`);
* `net_exp_le`: `(16/η)^r e^{-Θ r/3200} ≤ e^{-r}` (since `Θ/3200 - 1 = 57/4`);
* `two_exp_neg_eleven_le`: `2 e^{-11} ≤ 1/20000` (via `40000 ≤ 2.718¹¹ < e¹¹`);
* `loc_M_check`: `Θ ≤ M (ε-η)²/(1+η)²` (rational);
* `sqrt_lambdaSq_le`, `loc_lambda_check`: `√(λ²) ≤ 51855/10⁶` and
  `(51855/10⁶ + 50η)² ≤ (2/81)(ε-η)²`, which give `λ + 50η < c_ph (ε - η)` (rational).
-/

namespace SparseStack

namespace Loc

theorem exp_one_gt_2718 : (2.718 : ℝ) < Real.exp 1 :=
  lt_trans (by norm_num) Real.exp_one_gt_d9

/-- `1536000 < e^{57/4}`, i.e. `log(16/η) < 57/4` for `η = 1/96000`. -/
theorem lt_exp_57_div_4 : (1536000 : ℝ) < Real.exp (57 / 4) := by
  have h57 : Real.exp (57 / 4) ^ 4 = Real.exp 1 ^ 57 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have hpow : (2.718 : ℝ) ^ 57 < Real.exp 1 ^ 57 :=
    pow_lt_pow_left₀ exp_one_gt_2718 (by norm_num) (by norm_num)
  have hnum : (1536000 : ℝ) ^ 4 < 2.718 ^ 57 := by norm_num
  have h4 : (1536000 : ℝ) ^ 4 < Real.exp (57 / 4) ^ 4 := by
    rw [h57]
    exact hnum.trans hpow
  exact lt_of_pow_lt_pow_left₀ 4 (Real.exp_pos _).le h4

/-- `2 e^{-11} ≤ 1/20000`. -/
theorem two_exp_neg_eleven_le : 2 * Real.exp (-11) ≤ 1 / 20000 := by
  have h11 : Real.exp 11 = Real.exp 1 ^ 11 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (2.718 : ℝ) ^ 11 < Real.exp 1 ^ 11 :=
    pow_lt_pow_left₀ exp_one_gt_2718 (by norm_num) (by norm_num)
  have hbig : (40000 : ℝ) ≤ Real.exp 11 := by
    rw [h11]
    have h : (40000 : ℝ) ≤ 2.718 ^ 11 := by norm_num
    linarith
  have hpos : 0 < Real.exp 11 := Real.exp_pos _
  rw [Real.exp_neg, show (2 : ℝ) * (Real.exp 11)⁻¹ = 2 / Real.exp 11 by ring,
    div_le_div_iff₀ hpos (by norm_num)]
  linarith

/-- `(16/η)^r e^{-Θ r/3200} ≤ e^{-r}` for `η = 1/96000`, `Θ = 48800`. -/
theorem net_exp_le (r : ℕ) :
    ((16 : ℝ) / (1 / 96000)) ^ r * Real.exp (-((48800 : ℝ) * r) / 3200) ≤
      Real.exp (-(r : ℝ)) := by
  have h1 : (16 : ℝ) / (1 / 96000) * Real.exp (-(48800 : ℝ) / 3200) ≤ Real.exp (-1) := by
    have e : Real.exp (-1) = Real.exp (57 / 4) * Real.exp (-(48800 : ℝ) / 3200) := by
      rw [← Real.exp_add]
      norm_num
    rw [e, show (16 : ℝ) / (1 / 96000) = 1536000 by norm_num]
    exact mul_le_mul_of_nonneg_right lt_exp_57_div_4.le (Real.exp_pos _).le
  calc ((16 : ℝ) / (1 / 96000)) ^ r * Real.exp (-((48800 : ℝ) * r) / 3200)
      = ((16 : ℝ) / (1 / 96000) * Real.exp (-(48800 : ℝ) / 3200)) ^ r := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
    _ ≤ Real.exp (-1) ^ r := pow_le_pow_left₀ (by positivity) h1 r
    _ = Real.exp (-(r : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- `Θ ≤ M (ε - η)² / (1 + η)²`. -/
theorem loc_M_check :
    (48800 : ℝ) ≤ 440000 * ((1 / 3 - 1 / 96000) ^ 2 / (1 + 1 / 96000) ^ 2) := by
  norm_num

/-- `√(λ²) ≤ 51855/10⁶`. -/
theorem sqrt_lambdaSq_le : Real.sqrt (121 / 45000) ≤ 51855 / 1000000 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

/-- `(51855/10⁶ + 50 η)² ≤ (2/81) (ε - η)²`. -/
theorem loc_lambda_check :
    (51855 / 1000000 + 50 * (1 / 96000) : ℝ) ^ 2 ≤ 2 / 81 * (1 / 3 - 1 / 96000) ^ 2 := by
  norm_num

end Loc

end SparseStack
