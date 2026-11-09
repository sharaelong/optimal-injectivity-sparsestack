import SparseStack.Numerics.Params

/-!
# Numerical facts of Case B (paper, `prop:parameters`, lines 1243–1296, with `κ = 1`)

Proof plan (`L = log(e r)`, `ζ = numBlocks r`, `b = numBuckets r`, `q = ⌊ζ/2⌋`, `m = ⌈M r/q⌉`):
1. `C √L ≤ ζ < 104 L = 104 (√L)²` gives `√L > C/104 > 315`, hence `L ≥ 99225` and
   `ζ ≥ 315 C = 10321920`.
2. `r = e^{L-1} ≥ 1 + (L-1) + (L-1)²/2 ≥ 300 L` (as `L ≥ 700`); so `ζ < 104 L ≤ r`.
3. Natural-number arithmetic: `q ≤ ζ ≤ r`, `1000 q ≥ 499 ζ` (as `ζ ≥ 500`), `q ≥ 5·10⁶`,
   and with `b ζ ≥ K r`: `1000 b q ≥ 499 b ζ ≥ 499 K r`, i.e. `b q ≥ ρ₀ K r = K⋆ r ≥ Θ r`.
4. `m < M r/q + 1`, so `m q < M r + q`; then `8 m q < 8 M r + 8 q ≤ 8(M+1) r ≤ q r` gives
   `8 m ≤ r`, and `128 m q < 128 (M+1) r ≤ K⋆ r ≤ b q` gives `128 m ≤ b`.
5. `C⋆ √L ≤ ρ₀ C √L ≤ ρ₀ ζ ≤ q`, `q ≤ ζ/2 < 52 L < 256 L`, `ρ₀ ≤ q/ζ`.
-/

namespace SparseStack

/-- `r = e^{L-1} ≥ 300 L` once `L ≥ 700` (via `e^x ≥ 1 + x + x²/2`). -/
theorem r_ge_300_logER {r : ℕ} (hr : 2 ≤ r) (hL : 700 ≤ logER r) : 300 * logER r ≤ r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hlog : Real.log r = logER r - 1 := by rw [logER_eq (by omega)]; ring
  have hexp : (r : ℝ) = Real.exp (logER r - 1) := by rw [← hlog, Real.exp_log hr0]
  have hx : 0 ≤ logER r - 1 := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg hx
  rw [hexp]
  nlinarith

/-- Numerical facts of Case B (paper, lines 1243–1296 with `κ = 1`). Here `q = ⌊ζ/2⌋`,
`m = ⌈M r/q⌉`. -/
theorem caseB_params {r : ℕ} (hr : 2 ≤ r) (hL : 64 ≤ logER r)
    (hζ : (numBlocks r : ℝ) < 104 * logER r) :
    11 ≤ r ∧ 1 ≤ numBlocks r / 2 ∧ numBlocks r / 2 ≤ r ∧
      locTheta * r ≤ numBuckets r * (numBlocks r / 2) ∧
      1 ≤ locWidth r (numBlocks r / 2) ∧ 8 * locWidth r (numBlocks r / 2) ≤ r ∧
      16 * (8 * locWidth r (numBlocks r / 2)) ≤ numBuckets r ∧
      cStarRep * Real.sqrt (Real.log (Real.exp 1 * r)) ≤ (numBlocks r / 2 : ℕ) ∧
      ((numBlocks r / 2 : ℕ) : ℝ) < 256 * Real.log (Real.exp 1 * r) ∧
      kStarRep * r ≤ numBuckets r * (numBlocks r / 2) ∧
      rho0 ≤ ((numBlocks r / 2 : ℕ) : ℝ) / (numBlocks r : ℝ) := by
  have hLdef : Real.log (Real.exp 1 * r) = logER r := rfl
  rw [hLdef]
  have hsqrt := numBlocks_ge r
  rw [constC_real] at hsqrt
  have hbζ := numBuckets_mul_ge hr
  have hK : constK = 160000000 := rfl
  rw [hK] at hbζ
  have hζ2000 := numBlocks_ge_2000 hr
  have hlocM : (locM : ℝ) = 440000 := by norm_num [locM]
  set L := logER r with hLset
  set ζ := numBlocks r with hζset
  set b := numBuckets r with hbset
  set q := ζ / 2 with hqset
  set m := locWidth r q with hmset
  -- Step 1: `C √L ≤ ζ < 104 L` forces `√L > 315`, so `L ≥ 99225` and `ζ ≥ 10321920`.
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hL0
  have hss : s * s = L := Real.mul_self_sqrt hL0.le
  have hs315 : 315 < s := by nlinarith
  have hLbig : 99225 ≤ L := by nlinarith
  have hζbigR : (10321920 : ℝ) ≤ ζ := by linarith
  -- Step 2: `r = e^{L-1} ≥ 300 L`.
  have hrL : 300 * L ≤ r := r_ge_300_logER hr (by linarith)
  -- Step 3: natural-number facts.
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
  -- Step 4: real-number versions.
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hζ0 : (0 : ℝ) < ζ := by exact_mod_cast (show 0 < ζ by omega)
  have hq1R : (499 : ℝ) * ζ ≤ 1000 * q := by exact_mod_cast hq1
  have hq5R : (5000000 : ℝ) ≤ q := by exact_mod_cast hq5
  have hqrR : (q : ℝ) ≤ r := by exact_mod_cast hqr
  have h2qR : (2 : ℝ) * q ≤ ζ := by exact_mod_cast h2q
  have hbqR : (79840000 : ℝ) * r ≤ b * q := by exact_mod_cast hbq
  -- Step 5: the localization width `m = ⌈M r/q⌉ < M r/q + 1`.
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
  refine ⟨by omega, by omega, hqr, ?_, hm1, h8m, h128m, ?_, ?_, ?_, ?_⟩
  · -- `Θ r ≤ b q`
    show 48800 * r ≤ b * q
    omega
  · -- `C⋆ √L ≤ ρ₀ C √L ≤ ρ₀ ζ ≤ q`
    unfold cStarRep
    linarith
  · -- `q ≤ ζ/2 < 52 L < 256 L`
    linarith
  · -- `K⋆ r ≤ b q`
    exact hbq
  · -- `ρ₀ ≤ q/ζ`
    rw [le_div_iff₀ hζ0]
    unfold rho0
    linarith

end SparseStack
