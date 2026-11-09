import SparseStack.External.StackMoment
import SparseStack.Numerics.Params
import SparseFockFormal.MatrixTail

/-!
# Case A of `prop:parameters` (method D): `L < 64` or `ζ ≥ 104 L` (paper, lines 1187–1213)

Use eq. (stack-moment) on the full sketch with `U = Q`, `D = r`, `s = ζ`,
`p = ⌈(1/2) log(20 r)⌉`, so `2p + 1 ≤ L + 5`. If `L < 64`: `r + 2p + 1 ≤ 5r`,
`(2p+1)/ζ ≤ 13/C`, and (D1). If `L ≥ 64` and `ζ ≥ 104 L`: `r ≥ 300 L` gives
`r + 2p + 1 ≤ (101/100) r`, `(2p+1)/ζ ≤ 69/(64·104)`, and (D2). Then
`34(...) ≤ (4/11)(1 - α)`, Markov, `4/11 < e⁻¹`:
`P{λ_min(AᵀA) < α} ≤ P{‖G - I‖ ≥ 1 - α} ≤ r (4/11)^{2p} ≤ r e^{-2p} ≤ 1/20`.

## Formalization notes

* Rayleigh (`CaseA.quadraticLowerBound_of_norm_le`): with `G = AᵀA`, `‖G - I‖ ≤ 1 - α` gives
  `‖Ax‖² = xᵀGx ≥ ‖x‖² - ‖G - I‖ ‖x‖² ≥ α ‖x‖²` (Heidary's `MatrixTail.opNorm_le_iff_quadraticForm`).
* Markov on `‖G - I‖^{2p}` (`CaseA.prob_norm_ge_le`), then eq. (stack-moment) and the numerical
  bound `34 S ≤ (4/11)(1 - α)` give failure `≤ r (4/11)^{2p}` (`CaseA.failure_le`).
* Numerics. We use the cruder bound `r + 2p + 1 ≤ 5 r` (from `2p + 1 ≤ L + 5 ≤ r + 5`) in *both*
  sub-cases, hence `(r+2p+1)/(bζ) ≤ 5/K` (`CaseA.sketch_ratio_le`), and `(2p+1)/ζ ≤ 69/(64·104)`
  in both sub-cases (`CaseA.block_ratio_le`; for `L < 64` it follows from `ζ ≥ C√L ≥ C`). The
  single inequality `34 (√(5/K) + 5/K + 69/6656) < 0.3585 < (4/11)(1 - α)` (`CaseA.combined_le`)
  then covers both sub-cases, so `r ≥ 300 L` is not needed.
* `r (4/11)^{2p} ≤ 1/20` from `e ≤ 11/4` and `e^{2p} ≥ 20 r` (`CaseA.mul_four_elevenths_pow_le`).
-/

namespace SparseStack

open SparseFock

namespace CaseA

-- The L2 operator norm `‖·‖` on matrices (Heidary's convention), only inside the helpers, so
-- that the frozen statement of `caseA` below elaborates exactly as in the skeleton.
open scoped Matrix.Norms.L2Operator

/-! ### Rayleigh step and Markov -/

/-- Rayleigh: if `‖AᵀA - I‖ ≤ 1 - α` (L2 operator norm), then `α ‖x‖² ≤ ‖A x‖²` for every `x`. -/
theorem quadraticLowerBound_of_norm_le {k d : Type} [Fintype k] [Fintype d] [DecidableEq d]
    (A : Matrix k d ℝ) {α : ℝ} (h : ‖A.transpose * A - 1‖ ≤ 1 - α) :
    QuadraticLowerBound A α := by
  intro x
  have hε : 0 ≤ 1 - α := le_trans (norm_nonneg _) h
  have hG : (A.transpose * A).IsHermitian := by
    have := Matrix.isHermitian_conjTranspose_mul_self A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hherm : (A.transpose * A - 1).IsHermitian := hG.sub Matrix.isHermitian_one
  have hq := (MatrixTail.opNorm_le_iff_quadraticForm _ hherm (1 - α) hε).1 h (WithLp.toLp 2 x)
  rw [MatrixTail.quadraticForm_sub_one, MatrixTail.quadraticForm_transpose_mul_self,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hq
  simp only [MatrixTail.applyRectMatrix, PiLp.toLp_apply] at hq
  have e1 : dotProduct (A.mulVec x) (A.mulVec x) = ∑ i, (A.mulVec x) i ^ 2 := by
    simp only [dotProduct, sq]
  have e2 : dotProduct x x = ∑ i, x i ^ 2 := by
    simp only [dotProduct, sq]
  rw [e1, e2]
  rw [abs_le] at hq
  linarith [hq.1]

/-- Markov's inequality for a power of the operator norm of a random matrix. -/
theorem prob_norm_ge_le {Ω : Type} [Fintype Ω] (μ : FiniteLaw Ω) {d : Type} [Fintype d]
    [DecidableEq d] (M : Ω → Matrix d d ℝ) (q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    μ.prob {ω | ε ≤ ‖M ω‖} ≤ μ.expect (fun ω => ‖M ω‖ ^ q) / ε ^ q :=
  calc μ.prob {ω | ε ≤ ‖M ω‖} ≤ μ.prob {ω | ε ^ q ≤ ‖M ω‖ ^ q} :=
        μ.prob_mono fun _ hω => pow_le_pow_left₀ hε.le hω q
    _ ≤ μ.expect (fun ω => ‖M ω‖ ^ q) / ε ^ q :=
        μ.markov (fun _ => pow_nonneg (norm_nonneg _) q) (pow_pos hε q)

/-- Case A assembly (generic in the finite law `μ` and the random matrix `A`): Rayleigh, Markov
and a moment bound `E ‖AᵀA - I‖^{2p} ≤ D (34 S)^{2p}` with `34 S ≤ (4/11)(1 - α)` give
`P{α ‖x‖² ≤ ‖A x‖² fails for some x} ≤ D (4/11)^{2p}`. -/
theorem failure_le {Ω : Type} [Fintype Ω] (μ : FiniteLaw Ω) {k d : Type} [Fintype k]
    [Fintype d] [DecidableEq d] (A : Ω → Matrix k d ℝ) (D : ℝ) (p : ℕ)
    {α S : ℝ} (hα : α < 1) (hS0 : 0 ≤ S) (hS : 34 * S ≤ 4 / 11 * (1 - α)) (hD : 0 ≤ D)
    (hmom : μ.expect (fun ω => ‖(A ω).transpose * A ω - 1‖ ^ (2 * p)) ≤ D * (34 * S) ^ (2 * p)) :
    μ.prob {ω | QuadraticLowerBound (A ω) α}ᶜ ≤ D * (4 / 11) ^ (2 * p) := by
  have hε : 0 < 1 - α := by linarith
  have hne : (1 - α) ^ (2 * p) ≠ 0 := pow_ne_zero _ hε.ne'
  calc μ.prob {ω | QuadraticLowerBound (A ω) α}ᶜ
      ≤ μ.prob {ω | 1 - α ≤ ‖(A ω).transpose * A ω - 1‖} := by
        apply μ.prob_mono
        intro ω hω
        have hω' : ¬ QuadraticLowerBound (A ω) α := hω
        show 1 - α ≤ ‖(A ω).transpose * A ω - 1‖
        by_contra h
        exact hω' (quadraticLowerBound_of_norm_le _ (not_le.mp h).le)
    _ ≤ μ.expect (fun ω => ‖(A ω).transpose * A ω - 1‖ ^ (2 * p)) / (1 - α) ^ (2 * p) :=
        prob_norm_ge_le μ (fun ω => (A ω).transpose * A ω - 1) (2 * p) hε
    _ ≤ D * (34 * S) ^ (2 * p) / (1 - α) ^ (2 * p) :=
        div_le_div_of_nonneg_right hmom (pow_nonneg hε.le _)
    _ ≤ D * (4 / 11 * (1 - α)) ^ (2 * p) / (1 - α) ^ (2 * p) := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hε.le _)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hS _) hD
    _ = D * (4 / 11) ^ (2 * p) := by
        rw [mul_pow, ← mul_assoc, mul_div_assoc, div_self hne, mul_one]

/-! ### The moment order `p = ⌈(1/2) log(20 r)⌉` -/

/-- The moment order `p = ⌈(1/2) log(20 r)⌉`. -/
noncomputable def momentOrder (r : ℕ) : ℕ := Nat.ceil ((1 / 2 : ℝ) * Real.log (20 * (r : ℝ)))

theorem log_twenty_mul_pos {r : ℕ} (hr : 1 ≤ r) : 0 < Real.log (20 * (r : ℝ)) := by
  apply Real.log_pos
  have : (1 : ℝ) ≤ r := by exact_mod_cast hr
  linarith

theorem one_le_momentOrder {r : ℕ} (hr : 1 ≤ r) : 1 ≤ momentOrder r := by
  unfold momentOrder
  rw [Nat.one_le_ceil_iff]
  exact mul_pos (by norm_num) (log_twenty_mul_pos hr)

/-- `log(20 r) ≤ 2p`. -/
theorem log_le_two_momentOrder (r : ℕ) : Real.log (20 * (r : ℝ)) ≤ 2 * (momentOrder r : ℝ) := by
  have h : (1 / 2 : ℝ) * Real.log (20 * (r : ℝ)) ≤ (momentOrder r : ℝ) :=
    Nat.le_ceil ((1 / 2 : ℝ) * Real.log (20 * (r : ℝ)))
  linarith

/-- `log 20 < 3`, i.e. `20 < e³`. -/
theorem log_twenty_lt_three : Real.log 20 < 3 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h1]
  calc (20 : ℝ) < 2.7182818283 ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 3

/-- `2p + 1 ≤ L + 5`. -/
theorem two_momentOrder_add_one_le {r : ℕ} (hr : 1 ≤ r) :
    2 * (momentOrder r : ℝ) + 1 ≤ logER r + 5 := by
  have hlt : (momentOrder r : ℝ) < (1 / 2 : ℝ) * Real.log (20 * (r : ℝ)) + 1 :=
    Nat.ceil_lt_add_one (mul_pos (by norm_num) (log_twenty_mul_pos hr)).le
  have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlog : Real.log (20 * (r : ℝ)) = Real.log 20 + Real.log r :=
    Real.log_mul (by norm_num) hr0
  have hL := logER_eq hr
  have h3 := log_twenty_lt_three
  linarith

/-- `r (4/11)^{2p} ≤ r e^{-2p} ≤ 1/20`. -/
theorem mul_four_elevenths_pow_le {r : ℕ} (hr : 1 ≤ r) :
    (r : ℝ) * (4 / 11) ^ (2 * momentOrder r) ≤ 1 / 20 := by
  have hrpos : (0 : ℝ) < 20 * r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have h20 : (20 * r : ℝ) ≤ (11 / 4 : ℝ) ^ (2 * momentOrder r) := by
    calc (20 * r : ℝ) = Real.exp (Real.log (20 * r)) := (Real.exp_log hrpos).symm
      _ ≤ Real.exp ((2 * momentOrder r : ℕ) : ℝ) := by
          apply Real.exp_le_exp.mpr
          push_cast
          exact log_le_two_momentOrder r
      _ = Real.exp 1 ^ (2 * momentOrder r) := by
          rw [← Real.exp_nat_mul, mul_one]
      _ ≤ (11 / 4) ^ (2 * momentOrder r) := by
          apply pow_le_pow_left₀ (Real.exp_pos 1).le
          calc Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
            _ ≤ 11 / 4 := by norm_num
  have hmul : (11 / 4 : ℝ) ^ (2 * momentOrder r) * (4 / 11) ^ (2 * momentOrder r) = 1 := by
    rw [← mul_pow]
    norm_num
  calc (r : ℝ) * (4 / 11) ^ (2 * momentOrder r)
      = (20 * r) * (4 / 11) ^ (2 * momentOrder r) / 20 := by ring
    _ ≤ (11 / 4) ^ (2 * momentOrder r) * (4 / 11) ^ (2 * momentOrder r) / 20 := by gcongr
    _ = 1 / 20 := by rw [hmul]

/-! ### The two ratios of eq. (stack-moment) and the numerical bound -/

/-- `(r + 2p + 1)/(bζ) ≤ 5r/(Kr) = 5/K`, from `2p + 1 ≤ L + 5 ≤ r + 5 ≤ 4r` and `bζ ≥ Kr`. -/
theorem sketch_ratio_le {r : ℕ} (hr : 2 ≤ r) :
    ((r : ℝ) + 2 * (momentOrder r : ℝ) + 1) / ((numBuckets r : ℝ) * (numBlocks r : ℝ)) ≤
      5 / (constK : ℝ) := by
  have h1 := two_momentOrder_add_one_le (r := r) (by omega)
  have h2 := logER_le (r := r) (by omega)
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hnum : (r : ℝ) + 2 * (momentOrder r : ℝ) + 1 ≤ 5 * r := by linarith
  have hK : (constK : ℝ) * r ≤ (numBuckets r : ℝ) * (numBlocks r : ℝ) := by
    exact_mod_cast numBuckets_mul_ge hr
  have hKpos : (0 : ℝ) < constK := by norm_num [constK]
  have hden : 0 < (numBuckets r : ℝ) * (numBlocks r : ℝ) :=
    lt_of_lt_of_le (mul_pos hKpos (by linarith)) hK
  rw [div_le_div_iff₀ hden hKpos]
  calc ((r : ℝ) + 2 * (momentOrder r : ℝ) + 1) * constK ≤ 5 * r * constK :=
        mul_le_mul_of_nonneg_right hnum hKpos.le
    _ = 5 * (constK * r) := by ring
    _ ≤ 5 * ((numBuckets r : ℝ) * (numBlocks r : ℝ)) := by linarith

/-- `(2p + 1)/ζ ≤ 69/(64·104)` in Case A. For `L < 64`: `2p + 1 ≤ L + 5 < 69` and
`ζ ≥ C √L ≥ C = 32768`. For `L ≥ 64` and `ζ ≥ 104 L`: `(L + 5)/(104 L) ≤ 69/(64·104)`. -/
theorem block_ratio_le {r : ℕ} (hr : 2 ≤ r)
    (hreg : logER r < 64 ∨ 104 * logER r ≤ (numBlocks r : ℝ)) :
    (2 * (momentOrder r : ℝ) + 1) / (numBlocks r : ℝ) ≤ 69 / 6656 := by
  have h1 := two_momentOrder_add_one_le (r := r) (by omega)
  have hL1 := one_le_logER (r := r) (by omega)
  have hζ2000 : (2000 : ℝ) ≤ numBlocks r := by exact_mod_cast numBlocks_ge_2000 hr
  have hζpos : (0 : ℝ) < numBlocks r := by linarith
  rw [div_le_div_iff₀ hζpos (by norm_num)]
  by_cases hL : logER r < 64
  · have hC := numBlocks_ge r
    have hsqrt : 1 ≤ Real.sqrt (logER r) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hL1
    have hCval : (constC : ℝ) = 32768 := by norm_num [constC]
    rw [hCval] at hC
    linarith
  · have h104 : 104 * logER r ≤ (numBlocks r : ℝ) := hreg.resolve_left hL
    have hL64 : 64 ≤ logER r := not_lt.mp hL
    linarith

/-- The numerical bound behind (D1)/(D2):
`34 (√X + X + Y) ≤ 34 (√(5/K) + 5/K + 69/6656) < 0.3585 < (4/11)(1 - α)`. -/
theorem combined_le {X Y : ℝ} (hX : X ≤ 5 / (constK : ℝ)) (hY : Y ≤ 69 / 6656) :
    34 * (Real.sqrt X + X + Y) ≤ 4 / 11 * (1 - constAlpha) := by
  have hK : (constK : ℝ) = 160000000 := by norm_num [constK]
  rw [hK] at hX
  have hsq : Real.sqrt X ≤ 177 / 1000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    calc X ≤ 5 / 160000000 := hX
      _ ≤ (177 / 1000000) ^ 2 := by norm_num
  have hnum : (34 : ℝ) * (177 / 1000000 + 5 / 160000000 + 69 / 6656) ≤
      4 / 11 * (1 - 12256937 / 119880000000) := by norm_num
  unfold constAlpha
  linarith

end CaseA

/-- Case A: the probability clause (Rayleigh form) when `L < 64` or `ζ ≥ 104 L`. -/
theorem caseA {n r : ℕ} (hr : 2 ≤ r) (hrn : r ≤ n) (Q : Matrix (Fin n) (Fin r) ℝ)
    (hQ : Q.transpose * Q = 1)
    (hreg : logER r < 64 ∨ 104 * logER r ≤ (numBlocks r : ℝ)) :
    (19 / 20 : ℝ) ≤ uniformProb (SketchSample (numBlocks r) (numBuckets r) n)
      (fun ω => QuadraticLowerBound (sketchMatrix ω * Q) constAlpha) := by
  have hs1 : 1 ≤ numBlocks r := le_trans (by norm_num) (numBlocks_ge_2000 hr)
  have hb2 : 2 ≤ numBuckets r := two_le_numBuckets hr
  have hb0 : 0 < numBuckets r := by omega
  have hp1 : 1 ≤ CaseA.momentOrder r := CaseA.one_le_momentOrder (by omega)
  -- eq. (stack-moment) with `U = Q`, `D = r`, `s = ζ`, `p = ⌈(1/2) log(20 r)⌉`
  have hmom := stack_moment hs1 hb2 Q hQ (CaseA.momentOrder r) hp1
  -- `34 (√X + X + Y) ≤ (4/11)(1 - α)` with `X = (r+2p+1)/(bζ)`, `Y = (2p+1)/ζ`
  have hS := CaseA.combined_le (CaseA.sketch_ratio_le hr) (CaseA.block_ratio_le hr hreg)
  have hS0 : 0 ≤ Real.sqrt (((r : ℝ) + 2 * (CaseA.momentOrder r : ℝ) + 1) /
        ((numBuckets r : ℝ) * (numBlocks r : ℝ))) +
      ((r : ℝ) + 2 * (CaseA.momentOrder r : ℝ) + 1) / ((numBuckets r : ℝ) * (numBlocks r : ℝ)) +
      (2 * (CaseA.momentOrder r : ℝ) + 1) / (numBlocks r : ℝ) := by
    positivity
  have hα : constAlpha < 1 := by
    unfold constAlpha
    norm_num
  -- Markov: failure `≤ r (4/11)^{2p} ≤ 1/20`
  have hfail : (sketchLaw (numBlocks r) (numBuckets r) n hb0).prob
      {ω | QuadraticLowerBound (sketchMatrix ω * Q) constAlpha}ᶜ ≤
        (r : ℝ) * (4 / 11) ^ (2 * CaseA.momentOrder r) :=
    CaseA.failure_le (sketchLaw (numBlocks r) (numBuckets r) n hb0)
      (fun ω : SketchSample (numBlocks r) (numBuckets r) n => sketchMatrix ω * Q) (r : ℝ)
      (CaseA.momentOrder r) hα hS0 hS (Nat.cast_nonneg r) hmom
  have htail := CaseA.mul_four_elevenths_pow_le (r := r) (by omega)
  rw [uniformProb_eq_prob hb0]
  have hcompl := FiniteLaw.prob_compl (sketchLaw (numBlocks r) (numBuckets r) n hb0)
    {ω | QuadraticLowerBound (sketchMatrix ω * Q) constAlpha}
  linarith

end SparseStack
