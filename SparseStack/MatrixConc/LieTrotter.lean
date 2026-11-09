import Mathlib

/-!
# Lie product formula in a real Banach algebra

For `x y` in a complete normed `ℝ`-algebra `𝔸` with `‖1‖ = 1` we prove the Lie product
(Trotter) formula
`(exp (x / n) * exp (y / n)) ^ n → exp (x + y)` as `n → ∞`.

Proof:
* `F t = exp (t x) exp (t y)` and `G t = exp (t (x + y))` are differentiable at `0` with the same
  value `1` and the same derivative `x + y`; hence `H = F - G` satisfies `H t = o(t)`, i.e.
  `n ‖F (1/n) - G (1/n)‖ → 0`;
* `‖P ^ n - Q ^ n‖ ≤ n K ^ n ‖P - Q‖` whenever `‖P‖, ‖Q‖ ≤ K` and `1 ≤ K` (telescoping);
* `‖exp z‖ ≤ Real.exp ‖z‖`, so with `K = Real.exp ((‖x‖ + ‖y‖) / n)` we get `K ^ n = e^{‖x‖+‖y‖}`;
* `G (1/n) ^ n = exp (x + y)`.

We only use `NormedAlgebra ℝ 𝔸` (no `NormedAlgebra ℚ 𝔸` instance is required), so that the result
applies directly to real matrices with the `L2` operator norm.
-/

namespace SparseStack

namespace MatrixConc

open NormedSpace Filter Topology

section Banach

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `exp (x + y) = exp x * exp y` for commuting `x y` in a real Banach algebra. -/
theorem exp_add_of_commute_real {x y : 𝔸} (h : Commute x y) :
    exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

/-- `exp (n • x) = exp x ^ n` in a real Banach algebra. -/
theorem exp_nsmul_real (n : ℕ) (x : 𝔸) : exp (n • x) = exp x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, exp_zero]
  | succ n ih =>
    rw [succ_nsmul, pow_succ, exp_add_of_commute_real ((Commute.refl x).smul_left n), ih]

/-- The difference `exp (t x) exp (t y) - exp (t (x + y))` is `o(t)`: along `t = 1/n`,
`n ‖exp (x/n) exp (y/n) - exp ((x+y)/n)‖ → 0`. -/
theorem tendsto_lie_defect (x y : 𝔸) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ‖exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y) - exp ((n : ℝ)⁻¹ • (x + y))‖) atTop
      (𝓝 0) := by
  set H : ℝ → 𝔸 := fun t => exp (t • x) * exp (t • y) - exp (t • (x + y)) with hH
  have hHd : HasDerivAt H 0 0 := by
    have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) x 0).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) y 0)
    have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (x + y) 0
    have h3 := h1.sub h2
    simp only [zero_smul, exp_zero, one_mul, mul_one, sub_self] at h3
    exact h3
  have hH0 : H 0 = 0 := by simp [hH]
  have hslope := hHd.tendsto_slope_zero
  have hseq : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    simpa using this
  have h := (hslope.comp hseq).norm
  simp only [Function.comp_def, zero_add, hH0, sub_zero, inv_inv, norm_zero] at h
  refine h.congr' ?_
  filter_upwards with n
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]

variable [NormOneClass 𝔸]

omit [CompleteSpace 𝔸] in
/-- `‖exp x‖ ≤ Real.exp ‖x‖` in a real Banach algebra with `‖1‖ = 1`. -/
theorem norm_exp_le_exp_norm (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have hs : Summable fun n : ℕ => ‖((n.factorial : ℝ)⁻¹) • x ^ n‖ :=
    norm_expSeries_summable' (𝕂 := ℝ) x
  have hs' : Summable fun n : ℕ => ((n.factorial : ℝ)⁻¹) • ‖x‖ ^ n :=
    expSeries_summable' (𝕂 := ℝ) (‖x‖ : ℝ)
  rw [exp_eq_tsum ℝ, Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ]
  refine (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum (fun n => ?_) hs hs')
  rw [norm_smul, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- Telescoping: `‖P ^ n - Q ^ n‖ ≤ n K ^ n ‖P - Q‖` if `‖P‖, ‖Q‖ ≤ K` and `1 ≤ K`. -/
theorem norm_pow_sub_pow_le (P Q : 𝔸) {K : ℝ} (hK : 1 ≤ K) (hP : ‖P‖ ≤ K) (hQ : ‖Q‖ ≤ K)
    (n : ℕ) : ‖P ^ n - Q ^ n‖ ≤ n * K ^ n * ‖P - Q‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : P ^ (n + 1) - Q ^ (n + 1) = P ^ n * (P - Q) + (P ^ n - Q ^ n) * Q := by
      rw [pow_succ, pow_succ]; noncomm_ring
    have hPn : ‖P ^ n‖ ≤ K ^ n :=
      (norm_pow_le P n).trans (pow_le_pow_left₀ (norm_nonneg _) hP n)
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    have hd := norm_nonneg (P - Q)
    have hKK : K ^ n * ‖P - Q‖ ≤ K ^ n * K * ‖P - Q‖ := by
      apply mul_le_mul_of_nonneg_right _ hd
      calc K ^ n = K ^ n * 1 := (mul_one _).symm
        _ ≤ K ^ n * K := mul_le_mul_of_nonneg_left hK (pow_nonneg hK0 n)
    rw [e]
    calc ‖P ^ n * (P - Q) + (P ^ n - Q ^ n) * Q‖
        ≤ ‖P ^ n * (P - Q)‖ + ‖(P ^ n - Q ^ n) * Q‖ := norm_add_le _ _
      _ ≤ ‖P ^ n‖ * ‖P - Q‖ + ‖P ^ n - Q ^ n‖ * ‖Q‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ K ^ n * ‖P - Q‖ + (n * K ^ n * ‖P - Q‖) * K := by
          gcongr
      _ ≤ K ^ n * K * ‖P - Q‖ + (n * K ^ n * ‖P - Q‖) * K := by
          linarith
      _ = ((n + 1 : ℕ) : ℝ) * K ^ (n + 1) * ‖P - Q‖ := by
          push_cast; ring

/-- Quantitative Lie product estimate. -/
theorem lie_product_bound (x y : 𝔸) (n : ℕ) (hn : 1 ≤ n) :
    ‖(exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n - exp (x + y)‖ ≤
      Real.exp (‖x‖ + ‖y‖) * ((n : ℝ) *
        ‖exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y) - exp ((n : ℝ)⁻¹ • (x + y))‖) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn0.le
  have hK1 : 1 ≤ Real.exp ((n : ℝ)⁻¹ * (‖x‖ + ‖y‖)) := Real.one_le_exp (by positivity)
  have hP : ‖exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)‖ ≤
      Real.exp ((n : ℝ)⁻¹ * (‖x‖ + ‖y‖)) := by
    calc ‖exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)‖
        ≤ ‖exp ((n : ℝ)⁻¹ • x)‖ * ‖exp ((n : ℝ)⁻¹ • y)‖ := norm_mul_le _ _
      _ ≤ Real.exp ‖(n : ℝ)⁻¹ • x‖ * Real.exp ‖(n : ℝ)⁻¹ • y‖ :=
          mul_le_mul (norm_exp_le_exp_norm _) (norm_exp_le_exp_norm _) (norm_nonneg _)
            (Real.exp_pos _).le
      _ = Real.exp ((n : ℝ)⁻¹ * (‖x‖ + ‖y‖)) := by
          rw [← Real.exp_add, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, mul_add]
  have hQ : ‖exp ((n : ℝ)⁻¹ • (x + y))‖ ≤ Real.exp ((n : ℝ)⁻¹ * (‖x‖ + ‖y‖)) := by
    calc ‖exp ((n : ℝ)⁻¹ • (x + y))‖ ≤ Real.exp ‖(n : ℝ)⁻¹ • (x + y)‖ := norm_exp_le_exp_norm _
      _ ≤ Real.exp ((n : ℝ)⁻¹ * (‖x‖ + ‖y‖)) := by
          apply Real.exp_le_exp.mpr
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
          exact mul_le_mul_of_nonneg_left (norm_add_le x y) hs0
  have hQn : exp ((n : ℝ)⁻¹ • (x + y)) ^ n = exp (x + y) := by
    rw [← exp_nsmul_real, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn0.ne',
      one_smul]
  have hKn : Real.exp ((n : ℝ)⁻¹ * (‖x‖ + ‖y‖)) ^ n = Real.exp (‖x‖ + ‖y‖) := by
    rw [← Real.exp_nat_mul, ← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul]
  calc ‖(exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n - exp (x + y)‖
      = ‖(exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n -
          exp ((n : ℝ)⁻¹ • (x + y)) ^ n‖ := by rw [hQn]
    _ ≤ n * Real.exp ((n : ℝ)⁻¹ * (‖x‖ + ‖y‖)) ^ n *
          ‖exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y) - exp ((n : ℝ)⁻¹ • (x + y))‖ :=
        norm_pow_sub_pow_le _ _ hK1 hP hQ n
    _ = Real.exp (‖x‖ + ‖y‖) * ((n : ℝ) *
          ‖exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y) - exp ((n : ℝ)⁻¹ • (x + y))‖) := by
        rw [hKn]; ring

/-- **Lie product formula** in a real Banach algebra with `‖1‖ = 1`:
`(exp (x / n) * exp (y / n)) ^ n → exp (x + y)`. -/
theorem lie_product_formula (x y : 𝔸) :
    Tendsto (fun n : ℕ => (exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n) atTop
      (𝓝 (exp (x + y))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hupper := (tendsto_lie_defect x y).const_mul (Real.exp (‖x‖ + ‖y‖))
  rw [mul_zero] at hupper
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact lie_product_bound x y n hn

end Banach

end MatrixConc

end SparseStack
