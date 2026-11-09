import Mathlib

/-!
# Scalar numerics for the refined independent-entry norm estimate (W-HEID)

* `exp_half_mul_lt_22`: `e^{1/2} · 3(3+√2) < 22` (paper line 833, with `d^{1/(2p)} ≤ e^{1/2}`);
* `am_gm_half`: `a t ≤ (a + y)/2` from `(a t)² = a y` (paper line 846);
* `iid_final_numeric`: `(e-1)a + L + K(at + y + 2p + 1) ≤ 46(a + y + p)` for `K < 22`,
  `L ≤ p`, `p ≥ 64` (paper lines 835–846, with the diagonal bound `(e-1)a + log d` of the
  isotropic matrix Chernoff inequality in place of matrix Bernstein).
-/

namespace SparseStack.HeidBridge

/-- `e^{1/2} < 1.6488`. -/
theorem exp_half_lt : Real.exp (1 / 2) < 1.6488 := by
  rw [Real.exp_half, Real.sqrt_lt' (by norm_num)]
  calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    _ < 1.6488 ^ 2 := by norm_num

/-- `e^{1/2} · 3(3+√2) < 22`. -/
theorem exp_half_mul_lt_22 : Real.exp (1 / 2) * (3 * (3 + Real.sqrt 2)) < 22 := by
  have hs2 : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h1 : 3 * (3 + Real.sqrt 2) < 3 * (3 + 1.4143) := by linarith
  have h2 : Real.exp (1 / 2) * (3 * (3 + Real.sqrt 2)) < 1.6488 * (3 * (3 + 1.4143)) :=
    mul_lt_mul'' exp_half_lt h1 (Real.exp_pos _).le (by positivity)
  calc Real.exp (1 / 2) * (3 * (3 + Real.sqrt 2)) < 1.6488 * (3 * (3 + 1.4143)) := h2
    _ < 22 := by norm_num

/-- AM–GM in the form used for `22 √(a D_p/B) ≤ 11 a + 11 D_p/B`. -/
theorem am_gm_half {a t y : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hy : 0 ≤ y)
    (h : (a * t) ^ 2 = a * y) : a * t ≤ (a + y) / 2 := by
  have hsq : (a * t) ^ 2 ≤ ((a + y) / 2) ^ 2 := by
    rw [h]
    nlinarith [sq_nonneg (a - y)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hsq

/-- The final scalar inequality of the refined `lem:iid-norm`. -/
theorem iid_final_numeric {a y p L t K : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) (hp : 64 ≤ p)
    (hL : L ≤ p) (ht : 0 ≤ t) (hat : a * t ≤ (a + y) / 2) (hK : K < 22) :
    (Real.exp 1 - 1) * a + L + K * (a * t + y + (2 * p + 1)) ≤ 46 * (a + y + p) := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hbr : 0 ≤ a * t + y + (2 * p + 1) := by
    have : 0 ≤ a * t := mul_nonneg ha ht
    linarith
  have h1 : K * (a * t + y + (2 * p + 1)) ≤ 22 * (a * t + y + (2 * p + 1)) :=
    mul_le_mul_of_nonneg_right hK.le hbr
  have h2 : (Real.exp 1 - 1) * a ≤ 1.7182818286 * a :=
    mul_le_mul_of_nonneg_right (by linarith) ha
  linarith

end SparseStack.HeidBridge
