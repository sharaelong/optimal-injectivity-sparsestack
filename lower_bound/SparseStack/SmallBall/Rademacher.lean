import SparseStack.Prob.Toolkit
import SparseStack.Basic.Defs

/-!
# Rademacher sums: second and fourth moments, small ball (helper for `lem:smallball`)

Paper, proof of Lemma `lem:smallball`, lines 257–268. For independent uniform sign bits `y k`
and real coefficients `c k`, write `ε_k = signValue (y k)` and `Y = ∑ c_k ε_k`.

* `rademacher_moments`: `E Y² = ∑ c_k²` and `E Y⁴ ≤ 3 (∑ c_k²)²`. Induction on the support:
  splitting off one coordinate `a`, the odd cross terms `E[Y^m ε_a]` vanish by independence
  (`expect_mul_of_dependsOn`) and `E ε_a = 0`, so `E(c ε_a + Y)⁴ = c⁴ + 6 c² E Y² + E Y⁴`.
* `rademacher_smallball`: Paley–Zygmund with `θ = 1/3` gives `P{Y² ≥ (∑ c_k²)/3} ≥ 4/27`.

The paper conditions on the signs in `supp h` and writes a bucket output as `y + X₀`. Here the
whole bucket output is treated as one Rademacher sum. This gives the same bound without
conditioning: `E Y² = ∑_{bucket} w_i² ≥ a² v` replaces `E(y+X₀)² = y² + a²v`.
-/

open scoped BigOperators

namespace SparseStack

open SparseFock

noncomputable section

namespace SmallBallAux

/-- The law of independent uniform sign bits indexed by `ι`. -/
abbrev signsLaw (ι : Type*) [Fintype ι] [DecidableEq ι] : FiniteLaw (ι → Bool) :=
  FiniteLaw.independentProduct (fun _ : ι => uniformLaw Bool)

theorem signValue_sq (β : Bool) : signValue β ^ 2 = 1 := by
  cases β <;> norm_num [signValue]

theorem uniformLaw_expect_signValue : (uniformLaw Bool).expect signValue = 0 := by
  rw [uniformLaw_expect]
  simp [signValue]

theorem expect_signValue_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι) :
    (signsLaw ι).expect (fun y => signValue (y k)) = 0 := by
  rw [FiniteLaw.expect_independentProduct_apply (fun _ : ι => uniformLaw Bool) k signValue]
  exact uniformLaw_expect_signValue

/-- Odd cross terms vanish: if `a ∉ T`, then `E[(∑_{k ∈ T} c_k ε_k)^m ε_a] = 0`. -/
theorem expect_pow_mul_sign {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (T : Finset ι)
    {a : ι} (ha : a ∉ T) (m : ℕ) :
    (signsLaw ι).expect
        (fun y => (∑ k ∈ T, c k * signValue (y k)) ^ m * signValue (y a)) = 0 := by
  rw [expect_mul_of_dependsOn (fun _ : ι => uniformLaw Bool) T
    (fun y => (∑ k ∈ T, c k * signValue (y k)) ^ m) (fun y => signValue (y a))]
  · rw [expect_signValue_coord, mul_zero]
  · intro x y hxy
    have hsum : ∑ k ∈ T, c k * signValue (x k) = ∑ k ∈ T, c k * signValue (y k) :=
      Finset.sum_congr rfl (fun k hk => by rw [hxy k hk])
    simp only [hsum]
  · intro x y hxy
    simp only [hxy a ha]

/-- Second and fourth moments of a Rademacher sum. -/
theorem rademacher_moments {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ)
    (T : Finset ι) :
    (signsLaw ι).expect (fun y => (∑ k ∈ T, c k * signValue (y k)) ^ 2) = ∑ k ∈ T, c k ^ 2 ∧
      (signsLaw ι).expect (fun y => (∑ k ∈ T, c k * signValue (y k)) ^ 4) ≤
        3 * (∑ k ∈ T, c k ^ 2) ^ 2 := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    obtain ⟨ih2, ih4⟩ := ih
    have h1 := expect_pow_mul_sign c T ha 1
    have h3 := expect_pow_mul_sign c T ha 3
    simp only [Finset.sum_insert ha]
    constructor
    · have hpt : ∀ y : ι → Bool,
          (c a * signValue (y a) + ∑ k ∈ T, c k * signValue (y k)) ^ 2 =
            c a ^ 2 + 2 * c a * ((∑ k ∈ T, c k * signValue (y k)) ^ 1 * signValue (y a)) +
              (∑ k ∈ T, c k * signValue (y k)) ^ 2 := by
        intro y
        linear_combination c a ^ 2 * signValue_sq (y a)
      rw [FiniteLaw.expect_congr _ hpt, FiniteLaw.expect_add, FiniteLaw.expect_add,
        FiniteLaw.expect_const, FiniteLaw.expect_smul, h1, ih2]
      ring
    · have hpt : ∀ y : ι → Bool,
          (c a * signValue (y a) + ∑ k ∈ T, c k * signValue (y k)) ^ 4 =
            c a ^ 4 + 4 * c a ^ 3 * ((∑ k ∈ T, c k * signValue (y k)) ^ 1 * signValue (y a)) +
              6 * c a ^ 2 * (∑ k ∈ T, c k * signValue (y k)) ^ 2 +
              4 * c a * ((∑ k ∈ T, c k * signValue (y k)) ^ 3 * signValue (y a)) +
              (∑ k ∈ T, c k * signValue (y k)) ^ 4 := by
        intro y
        linear_combination (c a ^ 4 * (signValue (y a) ^ 2 + 1) +
          4 * c a ^ 3 * (∑ k ∈ T, c k * signValue (y k)) * signValue (y a) +
          6 * c a ^ 2 * (∑ k ∈ T, c k * signValue (y k)) ^ 2) * signValue_sq (y a)
      rw [FiniteLaw.expect_congr _ hpt, FiniteLaw.expect_add, FiniteLaw.expect_add,
        FiniteLaw.expect_add, FiniteLaw.expect_add, FiniteLaw.expect_const,
        FiniteLaw.expect_smul, FiniteLaw.expect_smul, FiniteLaw.expect_smul, h1, h3, ih2]
      nlinarith [ih4, pow_two_nonneg (c a ^ 2)]

/-- Small ball for a Rademacher sum (Paley–Zygmund with `θ = 1/3` and `E Y⁴ ≤ 3 (E Y²)²`):
`P{(∑ c_k ε_k)² ≥ (∑ c_k²)/3} ≥ 4/27`. -/
theorem rademacher_smallball {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) :
    4 / 27 ≤ (signsLaw ι).prob
      {y | (∑ k, c k ^ 2) / 3 ≤ (∑ k, c k * signValue (y k)) ^ 2} := by
  obtain ⟨h2, h4⟩ := rademacher_moments c Finset.univ
  have hA0 : 0 ≤ ∑ k, c k ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg (c k))
  rcases hA0.eq_or_lt with hA | hA
  · have hset : {y : ι → Bool | (∑ k, c k ^ 2) / 3 ≤ (∑ k, c k * signValue (y k)) ^ 2} =
        Set.univ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      rw [← hA, zero_div]
      positivity
    rw [hset, FiniteLaw.prob_univ]
    norm_num
  · have hpz : (1 - 1 / 3 : ℝ) ^ 2 *
          ((signsLaw ι).expect (fun y => (∑ k, c k * signValue (y k)) ^ 2)) ^ 2 ≤
        (signsLaw ι).prob {y | 1 / 3 * (signsLaw ι).expect
            (fun y => (∑ k, c k * signValue (y k)) ^ 2) ≤ (∑ k, c k * signValue (y k)) ^ 2} *
          (signsLaw ι).expect (fun y => ((∑ k, c k * signValue (y k)) ^ 2) ^ 2) :=
      paley_zygmund (signsLaw ι) (fun y => (∑ k, c k * signValue (y k)) ^ 2)
        (fun y => sq_nonneg _) (by norm_num) (by norm_num)
    rw [h2] at hpz
    have h4' : (signsLaw ι).expect (fun y => ((∑ k, c k * signValue (y k)) ^ 2) ^ 2) ≤
        3 * (∑ k, c k ^ 2) ^ 2 := by
      calc (signsLaw ι).expect (fun y => ((∑ k, c k * signValue (y k)) ^ 2) ^ 2)
          = (signsLaw ι).expect (fun y => (∑ k, c k * signValue (y k)) ^ 4) := by
            apply FiniteLaw.expect_congr
            intro y
            ring
        _ ≤ 3 * (∑ k, c k ^ 2) ^ 2 := h4
    have hset : {y : ι → Bool | 1 / 3 * ∑ k, c k ^ 2 ≤ (∑ k, c k * signValue (y k)) ^ 2} =
        {y | (∑ k, c k ^ 2) / 3 ≤ (∑ k, c k * signValue (y k)) ^ 2} := by
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro hy <;> linarith
    rw [hset] at hpz
    have hP0 := FiniteLaw.prob_nonneg (signsLaw ι)
      {y : ι → Bool | (∑ k, c k ^ 2) / 3 ≤ (∑ k, c k * signValue (y k)) ^ 2}
    have hmul := mul_le_mul_of_nonneg_left h4' hP0
    have hA2 : 0 < (∑ k, c k ^ 2) ^ 2 := by positivity
    by_contra hlt
    push Not at hlt
    have hlt' := mul_lt_mul_of_pos_right hlt hA2
    nlinarith

end SmallBallAux

end

end SparseStack
