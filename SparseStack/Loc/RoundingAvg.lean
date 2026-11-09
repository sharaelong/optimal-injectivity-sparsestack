import SparseStack.Loc.Basic
import SparseStack.Prob.Basic

/-!
# Unbiased randomized rounding as a finite average (W-LOC)

Paper, `lem:rounding`, lines 323–331. Each coordinate `x_i/h = ⌊x_i/h⌋ + θ_i` is rounded up with
probability `θ_i` and down with probability `1 - θ_i`, independently. The rounding error
`e_i = h (θ_i - [up])` is centered with variance `h² θ_i (1-θ_i) ≤ h²/4`, so
`E ‖T e‖² = ∑_{a,i} T_{ai}² E e_i² ≤ (h²/4) ‖T‖_F²` and some outcome is no larger than the mean.
The randomness is the finite product law `roundLaw` on `Fin r → Bool` (Heidary's
`FiniteLaw.independentProduct` of Bernoulli laws).
-/

namespace SparseStack

namespace Loc

open SparseFock

/-- Some outcome is no larger than the mean. -/
theorem exists_le_expect {α : Type*} [Fintype α] (μ : FiniteLaw α) (f : α → ℝ) :
    ∃ x, f x ≤ μ.expect f := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0⟩ : ∃ x, 0 < μ.weight x := by
    by_contra h
    push Not at h
    have h1 : ∑ x, μ.weight x ≤ 0 := Finset.sum_nonpos (fun x _ => h x)
    rw [μ.sum_weight] at h1
    linarith
  have hpos : 0 < ∑ x, μ.weight x * (f x - μ.expect f) := by
    apply Finset.sum_pos' (fun x _ => mul_nonneg (μ.weight_nonneg x) (sub_nonneg.mpr (hcon x).le))
    exact ⟨x0, Finset.mem_univ _, mul_pos hx0 (sub_pos.mpr (hcon x0))⟩
  have hzero : ∑ x, μ.weight x * (f x - μ.expect f) = 0 := by
    have h := μ.expect_sub f (fun _ => μ.expect f)
    rw [FiniteLaw.expect_const, sub_self] at h
    exact h
  linarith

/-- Bernoulli law on `Bool`: `true` with probability `θ`. -/
noncomputable def bernLaw (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : FiniteLaw Bool where
  weight b := if b then θ else 1 - θ
  weight_nonneg b := by
    cases b
    · simp only [Bool.false_eq_true, if_false]
      linarith
    · simp only [if_true]
      exact h0
  sum_weight := by
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    ring

theorem bernLaw_expect (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (f : Bool → ℝ) :
    (bernLaw θ h0 h1).expect f = θ * f true + (1 - θ) * f false := by
  unfold FiniteLaw.expect
  rw [Fintype.sum_bool]
  simp [bernLaw]

/-- Rounding error `h (θ - [b])` of one coordinate for the outcome `b` (`true` = round up). -/
noncomputable def rerr (h θ : ℝ) (b : Bool) : ℝ := h * (θ - if b then 1 else 0)

theorem expect_rerr (h θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (bernLaw θ h0 h1).expect (rerr h θ) = 0 := by
  rw [bernLaw_expect]
  simp only [rerr, if_true, Bool.false_eq_true, if_false]
  ring

theorem expect_rerr_sq_le (h θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (bernLaw θ h0 h1).expect (fun b => rerr h θ b ^ 2) ≤ h ^ 2 / 4 := by
  rw [bernLaw_expect]
  simp only [rerr, if_true, Bool.false_eq_true, if_false]
  nlinarith [mul_nonneg (sq_nonneg h) (sq_nonneg (θ - 1 / 2))]

variable {r : ℕ}

/-- Independent unbiased rounding of all coordinates. -/
noncomputable def roundLaw (θ : Fin r → ℝ) (h0 : ∀ i, 0 ≤ θ i) (h1 : ∀ i, θ i ≤ 1) :
    FiniteLaw (Fin r → Bool) :=
  FiniteLaw.independentProduct (fun i => bernLaw (θ i) (h0 i) (h1 i))

/-- Distinct coordinate errors are uncorrelated. -/
theorem expect_rerr_mul_of_ne (h : ℝ) (θ : Fin r → ℝ) (h0 : ∀ i, 0 ≤ θ i)
    (h1 : ∀ i, θ i ≤ 1) {i j : Fin r} (hij : i ≠ j) :
    (roundLaw θ h0 h1).expect (fun σ => rerr h (θ i) (σ i) * rerr h (θ j) (σ j)) = 0 := by
  have hf := FiniteLaw.expect_independentProduct_factorizes_on
    (fun l => bernLaw (θ l) (h0 l) (h1 l)) {i, j} (fun l b => rerr h (θ l) b)
  simp only [Finset.prod_pair hij, expect_rerr, zero_mul] at hf
  exact hf

/-- Each coordinate error has second moment at most `h²/4`. -/
theorem expect_rerr_mul_self_le (h : ℝ) (θ : Fin r → ℝ) (h0 : ∀ i, 0 ≤ θ i)
    (h1 : ∀ i, θ i ≤ 1) (i : Fin r) :
    (roundLaw θ h0 h1).expect (fun σ => rerr h (θ i) (σ i) * rerr h (θ i) (σ i)) ≤
      h ^ 2 / 4 := by
  have ha := FiniteLaw.expect_independentProduct_apply
    (fun l => bernLaw (θ l) (h0 l) (h1 l)) i (fun b => rerr h (θ i) b ^ 2)
  calc (roundLaw θ h0 h1).expect (fun σ => rerr h (θ i) (σ i) * rerr h (θ i) (σ i))
      = (roundLaw θ h0 h1).expect (fun σ => rerr h (θ i) (σ i) ^ 2) :=
        FiniteLaw.expect_congr _ (fun σ => by ring)
    _ = (bernLaw (θ i) (h0 i) (h1 i)).expect (fun b => rerr h (θ i) b ^ 2) := ha
    _ ≤ h ^ 2 / 4 := expect_rerr_sq_le h (θ i) (h0 i) (h1 i)

/-- `E ‖T e‖² ≤ (h²/4) ‖T‖_F²` for the rounding error vector `e`. -/
theorem expect_sqNorm_mulVec_rerr_le {k : Type} [Fintype k] (T : Matrix k (Fin r) ℝ) (h : ℝ)
    (θ : Fin r → ℝ) (h0 : ∀ i, 0 ≤ θ i) (h1 : ∀ i, θ i ≤ 1) :
    (roundLaw θ h0 h1).expect (fun σ => sqNorm (T.mulVec (fun i => rerr h (θ i) (σ i)))) ≤
      h ^ 2 / 4 * frobSq T := by
  have hexp : ∀ σ : Fin r → Bool, sqNorm (T.mulVec (fun i => rerr h (θ i) (σ i))) =
      ∑ a, ∑ i, ∑ j, (T a i * T a j) * (rerr h (θ i) (σ i) * rerr h (θ j) (σ j)) := by
    intro σ
    rw [sqNorm_eq_sum_sq]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Matrix.mulVec, dotProduct]
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [FiniteLaw.expect_congr _ hexp]
  simp only [expect_sum, FiniteLaw.expect_smul]
  have hdiag : ∀ a i, ∑ j, T a i * T a j *
      (roundLaw θ h0 h1).expect (fun σ => rerr h (θ i) (σ i) * rerr h (θ j) (σ j)) ≤
      T a i ^ 2 * (h ^ 2 / 4) := by
    intro a i
    rw [Finset.sum_eq_single i]
    · have hle := expect_rerr_mul_self_le h θ h0 h1 i
      have hTa : 0 ≤ T a i * T a i := mul_self_nonneg _
      calc T a i * T a i *
            (roundLaw θ h0 h1).expect (fun σ => rerr h (θ i) (σ i) * rerr h (θ i) (σ i))
          ≤ T a i * T a i * (h ^ 2 / 4) := mul_le_mul_of_nonneg_left hle hTa
        _ = T a i ^ 2 * (h ^ 2 / 4) := by ring
    · intro j _ hji
      rw [expect_rerr_mul_of_ne h θ h0 h1 (Ne.symm hji), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  calc ∑ a, ∑ i, ∑ j, T a i * T a j *
        (roundLaw θ h0 h1).expect (fun σ => rerr h (θ i) (σ i) * rerr h (θ j) (σ j))
      ≤ ∑ a, ∑ i, T a i ^ 2 * (h ^ 2 / 4) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun i _ => hdiag a i))
    _ = h ^ 2 / 4 * frobSq T := by
        unfold frobSq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- Unbiased lattice rounding: for `h > 0`, every `x` has a lattice point `h v` (`v ∈ ℤ^r`) with
coordinatewise error at most `h` and `‖T (x - h v)‖² ≤ (h²/4) ‖T‖_F²`. -/
theorem exists_round {k : Type} [Fintype k] (T : Matrix k (Fin r) ℝ) {h : ℝ} (hh : 0 < h)
    (x : Fin r → ℝ) :
    ∃ v : Fin r → ℤ, (∀ i, |x i - h * (v i : ℝ)| ≤ h) ∧
      sqNorm (T.mulVec (fun i => x i - h * (v i : ℝ))) ≤ h ^ 2 / 4 * frobSq T := by
  have h0 : ∀ i, 0 ≤ Int.fract (x i / h) := fun i => Int.fract_nonneg _
  have h1 : ∀ i, Int.fract (x i / h) ≤ 1 := fun i => (Int.fract_lt_one _).le
  obtain ⟨σ, hσ⟩ := exists_le_expect (roundLaw (fun i => Int.fract (x i / h)) h0 h1)
    (fun σ => sqNorm (T.mulVec (fun i => rerr h (Int.fract (x i / h)) (σ i))))
  have key : ∀ i, x i - h * (((⌊x i / h⌋ + if σ i then 1 else 0 : ℤ)) : ℝ) =
      rerr h (Int.fract (x i / h)) (σ i) := by
    intro i
    obtain ⟨u, hu⟩ : ∃ u, u = x i / h := ⟨_, rfl⟩
    have hx : x i = h * u := by rw [hu, mul_div_cancel₀ _ hh.ne']
    rw [← hu, ← Int.self_sub_floor, hx]
    unfold rerr
    split_ifs <;> push_cast <;> ring
  refine ⟨fun i => ⌊x i / h⌋ + if σ i then 1 else 0, fun i => ?_, ?_⟩
  · show |x i - h * (((⌊x i / h⌋ + if σ i then 1 else 0 : ℤ)) : ℝ)| ≤ h
    rw [key i]
    unfold rerr
    rw [abs_mul, abs_of_pos hh]
    have hθ0 := h0 i
    have hθ1 : Int.fract (x i / h) < 1 := Int.fract_lt_one _
    have hb : |Int.fract (x i / h) - (if σ i then 1 else 0)| ≤ 1 := by
      rw [abs_le]
      split_ifs <;> constructor <;> linarith
    calc h * |Int.fract (x i / h) - (if σ i then 1 else 0)| ≤ h * 1 :=
          mul_le_mul_of_nonneg_left hb hh.le
      _ = h := mul_one h
  · have heq : (fun i => x i - h * (((⌊x i / h⌋ + if σ i then 1 else 0 : ℤ)) : ℝ)) =
        fun i => rerr h (Int.fract (x i / h)) (σ i) := funext key
    show sqNorm (T.mulVec (fun i => x i - h * (((⌊x i / h⌋ + if σ i then 1 else 0 : ℤ)) : ℝ))) ≤
      h ^ 2 / 4 * frobSq T
    rw [heq]
    exact hσ.trans (expect_sqNorm_mulVec_rerr_le T h (fun i => Int.fract (x i / h)) h0 h1)

end Loc

end SparseStack
