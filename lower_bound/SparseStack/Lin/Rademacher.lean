import Mathlib
import SparseFockFormal.FiniteProbability

/-!
# Rademacher vectors (helpers for `thm:linearization`)

The paper's Gaussian vector `x ~ N(0, R)` (lines 488–493) is replaced by `x = R^{1/2} ε` with `ε`
uniform on `{±1}^N` (encoded by `Fin N → Bool`). This file provides the uniform law `radLaw N`
and the moments of Rademacher sums `g = ∑_p c_p ε_p`:
* `expect_sgn_mul_sgn`: `E ε_p ε_q = δ_pq`;
* `rad_cross_moment`: `E (∑ a_p ε_p)(∑ b_q ε_q) = ∑ a_p b_p`;
* `rad_second_moment`: `E g² = ∑ c_p²`;
* `rad_fourth_moment`: `E g⁴ ≤ 3 (∑ c_p²)²`.

Proof idea: flipping one sign is a weight-preserving involution of the sample space, so an odd
power of the flipped sign times a function not depending on it averages to zero
(`sum_mul_sgn_eq_zero`). The fourth moment then follows by induction over the support:
`E (g + c ε_j)⁴ = E g⁴ + 6 c² E g² + c⁴ ≤ 3 (E g² + c²)²`.
-/

namespace SparseStack.Lin

open SparseFock

/-! ## Signs and flips -/

/-- The sign `±1` of a bit: `true ↦ 1`, `false ↦ -1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma sgn_true : sgn true = 1 := rfl

@[simp] lemma sgn_false : sgn false = -1 := rfl

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> norm_num [sgn]

lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by
  cases b <;> norm_num [sgn]

lemma sgn_not (b : Bool) : sgn (!b) = -sgn b := by
  cases b <;> norm_num [sgn]

/-- Flip the `j`-th bit of a sign vector. -/
def flipAt {N : ℕ} (j : Fin N) (ε : Fin N → Bool) : Fin N → Bool :=
  Function.update ε j (!ε j)

lemma flipAt_apply_self {N : ℕ} (j : Fin N) (ε : Fin N → Bool) : flipAt j ε j = !ε j := by
  simp [flipAt]

lemma flipAt_apply_ne {N : ℕ} {j p : Fin N} (h : p ≠ j) (ε : Fin N → Bool) :
    flipAt j ε p = ε p := by
  simp [flipAt, Function.update_of_ne h]

lemma flipAt_involutive {N : ℕ} (j : Fin N) : Function.Involutive (flipAt j) := by
  intro ε
  funext p
  by_cases hp : p = j
  · subst hp
    simp [flipAt_apply_self]
  · rw [flipAt_apply_ne hp, flipAt_apply_ne hp]

/-- If `F` does not see the `j`-th sign, then `∑_ε F(ε) ε_j = 0`. -/
lemma sum_mul_sgn_eq_zero {N : ℕ} (j : Fin N) (F : (Fin N → Bool) → ℝ)
    (hF : ∀ ε, F (flipAt j ε) = F ε) :
    ∑ ε, F ε * sgn (ε j) = 0 := by
  have h := Equiv.sum_comp (Function.Involutive.toPerm (flipAt j) (flipAt_involutive j))
    (fun ε => F ε * sgn (ε j))
  simp only [Function.Involutive.coe_toPerm, hF, flipAt_apply_self, sgn_not, mul_neg,
    Finset.sum_neg_distrib] at h
  linarith

/-! ## The uniform law on sign vectors -/

lemma card_signs_ne_zero (N : ℕ) : (Fintype.card (Fin N → Bool) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

lemma card_signs_pos (N : ℕ) : (0 : ℝ) < (Fintype.card (Fin N → Bool) : ℝ) :=
  Nat.cast_pos.mpr Fintype.card_pos

/-- The uniform law on sign vectors `Fin N → Bool` (independent fair signs). -/
noncomputable def radLaw (N : ℕ) : FiniteLaw (Fin N → Bool) where
  weight _ := (Fintype.card (Fin N → Bool) : ℝ)⁻¹
  weight_nonneg _ := inv_nonneg.mpr (card_signs_pos N).le
  sum_weight := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (card_signs_ne_zero N)

lemma radLaw_expect (N : ℕ) (f : (Fin N → Bool) → ℝ) :
    (radLaw N).expect f = (Fintype.card (Fin N → Bool) : ℝ)⁻¹ * ∑ ε, f ε := by
  simp only [FiniteLaw.expect, radLaw, Finset.mul_sum]

/-- Linearity of a finite expectation over a finite sum. -/
lemma expect_finset_sum {Ω ι : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (s : Finset ι)
    (f : ι → Ω → ℝ) : μ.expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, μ.expect (f i) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_comm

/-! ## Second moments -/

/-- `E ε_p ε_q = δ_pq`. -/
lemma expect_sgn_mul_sgn {N : ℕ} (p q : Fin N) :
    (radLaw N).expect (fun ε => sgn (ε p) * sgn (ε q)) = if p = q then 1 else 0 := by
  split_ifs with hpq
  · subst hpq
    simp only [sgn_mul_self, FiniteLaw.expect_const]
  · rw [radLaw_expect, sum_mul_sgn_eq_zero q (fun ε => sgn (ε p))
      (fun ε => by simp only [flipAt_apply_ne hpq]), mul_zero]

/-- `E (∑ a_p ε_p)(∑ b_q ε_q) = ∑ a_p b_p`. -/
lemma rad_cross_moment {N : ℕ} (a b : Fin N → ℝ) :
    (radLaw N).expect (fun ε => (∑ p, a p * sgn (ε p)) * (∑ q, b q * sgn (ε q))) =
      ∑ p, a p * b p := by
  have hexp : ∀ ε : Fin N → Bool, (∑ p, a p * sgn (ε p)) * (∑ q, b q * sgn (ε q)) =
      ∑ p, ∑ q, (a p * b q) * (sgn (ε p) * sgn (ε q)) := by
    intro ε
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    ring
  rw [FiniteLaw.expect_congr _ hexp, expect_finset_sum]
  have hinner : ∀ p, (radLaw N).expect (fun ε => ∑ q, (a p * b q) * (sgn (ε p) * sgn (ε q))) =
      a p * b p := by
    intro p
    rw [expect_finset_sum]
    simp only [FiniteLaw.expect_smul, expect_sgn_mul_sgn, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [hinner]

/-! ## Second and fourth moments of a Rademacher sum -/

/-- Partial Rademacher sum `∑_{p ∈ s} c_p ε_p`. -/
def radPartial {N : ℕ} (c : Fin N → ℝ) (s : Finset (Fin N)) (ε : Fin N → Bool) : ℝ :=
  ∑ p ∈ s, c p * sgn (ε p)

lemma radPartial_flip {N : ℕ} (c : Fin N → ℝ) {s : Finset (Fin N)} {j : Fin N} (hj : j ∉ s)
    (ε : Fin N → Bool) : radPartial c s (flipAt j ε) = radPartial c s ε := by
  unfold radPartial
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hpj : p ≠ j := fun h => hj (h ▸ hp)
  rw [flipAt_apply_ne hpj]

lemma radPartial_moments {N : ℕ} (c : Fin N → ℝ) (s : Finset (Fin N)) :
    ∑ ε, radPartial c s ε ^ 2 = (Fintype.card (Fin N → Bool) : ℝ) * ∑ p ∈ s, c p ^ 2 ∧
    ∑ ε, radPartial c s ε ^ 4 ≤
      3 * (Fintype.card (Fin N → Bool) : ℝ) * (∑ p ∈ s, c p ^ 2) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [radPartial]
  | insert j s hj ih =>
    obtain ⟨ih2, ih4⟩ := ih
    set M : ℝ := (Fintype.card (Fin N → Bool) : ℝ) with hMdef
    have hM : (∑ _ε : Fin N → Bool, (1 : ℝ)) = M := by
      simp [hMdef]
    have hM0 : 0 ≤ M := (card_signs_pos N).le
    have hsplit : ∀ ε, radPartial c (insert j s) ε = c j * sgn (ε j) + radPartial c s ε := by
      intro ε
      simp only [radPartial, Finset.sum_insert hj]
    have h1 : ∑ ε, radPartial c s ε * sgn (ε j) = 0 :=
      sum_mul_sgn_eq_zero j _ (radPartial_flip c hj)
    have h3 : ∑ ε, radPartial c s ε ^ 3 * sgn (ε j) = 0 :=
      sum_mul_sgn_eq_zero j (fun ε => radPartial c s ε ^ 3)
        (fun ε => by simp only [radPartial_flip c hj])
    have e2 : ∀ ε, radPartial c (insert j s) ε ^ 2 =
        radPartial c s ε ^ 2 + 2 * c j * (radPartial c s ε * sgn (ε j)) + c j ^ 2 * 1 := by
      intro ε
      rw [hsplit]
      have hσ := sgn_sq (ε j)
      linear_combination (c j ^ 2) * hσ
    have e4 : ∀ ε, radPartial c (insert j s) ε ^ 4 =
        radPartial c s ε ^ 4 + 4 * c j * (radPartial c s ε ^ 3 * sgn (ε j)) +
          6 * c j ^ 2 * radPartial c s ε ^ 2 + 4 * c j ^ 3 * (radPartial c s ε * sgn (ε j)) +
          c j ^ 4 * 1 := by
      intro ε
      rw [hsplit]
      have hσ := sgn_sq (ε j)
      linear_combination (6 * radPartial c s ε ^ 2 * c j ^ 2 +
        4 * radPartial c s ε * c j ^ 3 * sgn (ε j) + c j ^ 4 * (sgn (ε j) ^ 2 + 1)) * hσ
    have hA : 0 ≤ ∑ p ∈ s, c p ^ 2 := Finset.sum_nonneg (fun p _ => sq_nonneg (c p))
    rw [Finset.sum_insert hj]
    constructor
    · calc ∑ ε, radPartial c (insert j s) ε ^ 2
          = ∑ ε, radPartial c s ε ^ 2 + 2 * c j * ∑ ε, radPartial c s ε * sgn (ε j) +
              c j ^ 2 * ∑ _ε : Fin N → Bool, (1 : ℝ) := by
            simp only [e2, Finset.sum_add_distrib, Finset.mul_sum]
        _ = M * (c j ^ 2 + ∑ p ∈ s, c p ^ 2) := by
            rw [ih2, h1, hM]
            ring
    · calc ∑ ε, radPartial c (insert j s) ε ^ 4
          = ∑ ε, radPartial c s ε ^ 4 + 4 * c j * ∑ ε, radPartial c s ε ^ 3 * sgn (ε j) +
              6 * c j ^ 2 * ∑ ε, radPartial c s ε ^ 2 +
              4 * c j ^ 3 * ∑ ε, radPartial c s ε * sgn (ε j) +
              c j ^ 4 * ∑ _ε : Fin N → Bool, (1 : ℝ) := by
            simp only [e4, Finset.sum_add_distrib, Finset.mul_sum]
        _ = ∑ ε, radPartial c s ε ^ 4 + 6 * c j ^ 2 * (M * ∑ p ∈ s, c p ^ 2) + c j ^ 4 * M := by
            rw [h3, h1, ih2, hM]
            ring
        _ ≤ 3 * M * (∑ p ∈ s, c p ^ 2) ^ 2 + 6 * c j ^ 2 * (M * ∑ p ∈ s, c p ^ 2) +
              c j ^ 4 * M := by
            linarith [ih4]
        _ ≤ 3 * M * (c j ^ 2 + ∑ p ∈ s, c p ^ 2) ^ 2 := by
            have hc4 : 0 ≤ M * c j ^ 4 := mul_nonneg hM0 (by positivity)
            nlinarith [hc4]

/-- `E (∑ c_p ε_p)² = ∑ c_p²`. -/
theorem rad_second_moment {N : ℕ} (c : Fin N → ℝ) :
    (radLaw N).expect (fun ε => (∑ p, c p * sgn (ε p)) ^ 2) = ∑ p, c p ^ 2 := by
  rw [radLaw_expect]
  have h := (radPartial_moments c Finset.univ).1
  simp only [radPartial] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ (card_signs_ne_zero N), one_mul]

/-- `E (∑ c_p ε_p)⁴ ≤ 3 (∑ c_p²)²`. -/
theorem rad_fourth_moment {N : ℕ} (c : Fin N → ℝ) :
    (radLaw N).expect (fun ε => (∑ p, c p * sgn (ε p)) ^ 4) ≤ 3 * (∑ p, c p ^ 2) ^ 2 := by
  rw [radLaw_expect]
  have h := (radPartial_moments c Finset.univ).2
  simp only [radPartial] at h
  have hM := card_signs_pos N
  generalize (Fintype.card (Fin N → Bool) : ℝ) = M at h hM ⊢
  rw [inv_mul_le_iff₀ hM]
  linarith

/-! ## Matrix forms: the coordinates of `C ε` -/

/-- The sign vector `(ε_p)_p` as a real vector. -/
def sgnVec {N : ℕ} (ε : Fin N → Bool) : Fin N → ℝ := fun p => sgn (ε p)

/-- `E (C ε)_a (C ε)_b = (C Cᵀ)_ab`. -/
lemma rad_mulVec_cross {N : ℕ} {k : Type*} (C : Matrix k (Fin N) ℝ) (a b : k) :
    (radLaw N).expect (fun ε => (C.mulVec (sgnVec ε)) a * (C.mulVec (sgnVec ε)) b) =
      (C * C.transpose) a b := by
  have h := rad_cross_moment (fun p => C a p) (fun p => C b p)
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact h

/-- `E (C ε)_a² = ∑_p C_ap²`. -/
lemma rad_mulVec_sq {N : ℕ} {k : Type*} (C : Matrix k (Fin N) ℝ) (a : k) :
    (radLaw N).expect (fun ε => (C.mulVec (sgnVec ε)) a ^ 2) = ∑ p, C a p ^ 2 :=
  rad_second_moment (fun p => C a p)

/-- `E (C ε)_a⁴ ≤ 3 (E (C ε)_a²)²`. -/
lemma rad_mulVec_fourth {N : ℕ} {k : Type*} (C : Matrix k (Fin N) ℝ) (a : k) :
    (radLaw N).expect (fun ε => (C.mulVec (sgnVec ε)) a ^ 4) ≤
      3 * ((radLaw N).expect (fun ε => (C.mulVec (sgnVec ε)) a ^ 2)) ^ 2 := by
  rw [rad_mulVec_sq]
  exact rad_fourth_moment (fun p => C a p)

end SparseStack.Lin
