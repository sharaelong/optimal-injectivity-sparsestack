import SparseStack.Basic.Defs

/-!
# Helpers for `d_m`, Euclidean norms and isometries (W-LOC)

All helpers live in the namespace `SparseStack.Loc` to avoid clashes with other workers' files.

* `sqNorm_eq_sum_sq`, `sqNorm_nonneg`, `sq_le_sqNorm`, `frobSq_nonneg`;
* Minkowski for finite sums (`sqrt_sum_sq_add_le`) and for `sqNorm` (`sqrt_sqNorm_add_le`,
  `sqrt_sqNorm_sub_le`);
* isometries preserve `sqNorm` (`sqNorm_mulVec_of_isometry`);
* `d_m` is attained (`exists_distSparseSq_eq`) and bounded by every admissible set
  (`distSparseSq_le_of_card`);
* the exchange argument behind top-`m` removal (`topm_key`).
-/

namespace SparseStack

namespace Loc

open Matrix

theorem sqNorm_eq_sum_sq {ι : Type} [Fintype ι] (v : ι → ℝ) : sqNorm v = ∑ i, v i ^ 2 := by
  unfold sqNorm dotProduct
  exact Finset.sum_congr rfl (fun i _ => (sq (v i)).symm)

theorem sqNorm_nonneg {ι : Type} [Fintype ι] (v : ι → ℝ) : 0 ≤ sqNorm v := by
  rw [sqNorm_eq_sum_sq]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem sq_le_sqNorm {ι : Type} [Fintype ι] (v : ι → ℝ) (i : ι) : v i ^ 2 ≤ sqNorm v := by
  rw [sqNorm_eq_sum_sq]
  exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem frobSq_nonneg {k l : Type} [Fintype k] [Fintype l] (A : Matrix k l ℝ) : 0 ≤ frobSq A := by
  unfold frobSq
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

/-- Minkowski's inequality for finite sums. -/
theorem sqrt_sum_sq_add_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    √(∑ i ∈ s, (f i + g i) ^ 2) ≤ √(∑ i ∈ s, f i ^ 2) + √(∑ i ∈ s, g i ^ 2) := by
  have hA : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB : 0 ≤ ∑ i ∈ s, g i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt s f g
  rw [Real.sqrt_le_left (by positivity)]
  have hexp : ∑ i ∈ s, (f i + g i) ^ 2 =
      ∑ i ∈ s, f i ^ 2 + 2 * ∑ i ∈ s, f i * g i + ∑ i ∈ s, g i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hexp, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  nlinarith [hCS]

theorem sqrt_sqNorm_add_le {ι : Type} [Fintype ι] (u v : ι → ℝ) :
    √(sqNorm (u + v)) ≤ √(sqNorm u) + √(sqNorm v) := by
  simp only [sqNorm_eq_sum_sq, Pi.add_apply]
  exact sqrt_sum_sq_add_le Finset.univ u v

theorem sqNorm_neg {ι : Type} [Fintype ι] (v : ι → ℝ) : sqNorm (-v) = sqNorm v := by
  simp [sqNorm_eq_sum_sq]

theorem sqrt_sqNorm_sub_le {ι : Type} [Fintype ι] (u v : ι → ℝ) :
    √(sqNorm (u - v)) ≤ √(sqNorm u) + √(sqNorm v) := by
  have h := sqrt_sqNorm_add_le u (-v)
  rwa [← sub_eq_add_neg, sqNorm_neg] at h

/-- An isometry (`QᵀQ = I`) preserves squared Euclidean norms. -/
theorem sqNorm_mulVec_of_isometry {n r : ℕ} (Q : Matrix (Fin n) (Fin r) ℝ)
    (hQ : Q.transpose * Q = 1) (v : Fin r → ℝ) : sqNorm (Q.mulVec v) = sqNorm v := by
  unfold sqNorm
  rw [Matrix.dotProduct_mulVec,
    show Matrix.vecMul (Q.mulVec v) Q = Q.transpose.mulVec (Q.mulVec v) from
      (Matrix.mulVec_transpose Q _).symm,
    Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]

/-- `d_m(z)²` is at most the energy outside any admissible set `I` (`|I| ≤ m`). -/
theorem distSparseSq_le_of_card (m : ℕ) {n : ℕ} (z : Fin n → ℝ) (I : Finset (Fin n))
    (hI : I.card ≤ m) : distSparseSq m z ≤ ∑ i ∈ Iᶜ, z i ^ 2 := by
  unfold distSparseSq
  exact ciInf_le (Set.finite_range _).bddBelow (⟨I, hI⟩ : {I : Finset (Fin n) // I.card ≤ m})

/-- The minimum defining `d_m(z)²` is attained. -/
theorem exists_distSparseSq_eq (m : ℕ) {n : ℕ} (z : Fin n → ℝ) :
    ∃ I : Finset (Fin n), I.card ≤ m ∧ distSparseSq m z = ∑ i ∈ Iᶜ, z i ^ 2 := by
  have : Nonempty {I : Finset (Fin n) // I.card ≤ m} := ⟨⟨∅, by simp⟩⟩
  obtain ⟨I, hI⟩ := exists_eq_ciInf_of_finite
    (f := fun I : {I : Finset (Fin n) // I.card ≤ m} => ∑ i ∈ (I.1)ᶜ, z i ^ 2)
  refine ⟨I.1, I.2, ?_⟩
  unfold distSparseSq
  exact hI.symm

/-- Exchange argument for top-`m` removal: if `I` (with `|I| ≤ m`) maximizes the retained energy
`∑_{j ∈ I} w_j²` among sets of size `≤ m`, then every `i ∉ I` has `m w_i² ≤ ‖w‖²`. -/
theorem topm_key {n m : ℕ} (w : Fin n → ℝ) (I : Finset (Fin n)) (hI : I.card ≤ m)
    (hmax : ∀ J : Finset (Fin n), J.card ≤ m → ∑ j ∈ J, w j ^ 2 ≤ ∑ j ∈ I, w j ^ 2)
    (i : Fin n) (hi : i ∉ I) : (m : ℝ) * w i ^ 2 ≤ ∑ j, w j ^ 2 := by
  have h1 : ∀ j ∈ I, w i ^ 2 ≤ w j ^ 2 := by
    intro j hj
    have hi' : i ∉ I.erase j := fun h => hi (Finset.mem_of_mem_erase h)
    have hpos : 0 < I.card := Finset.card_pos.mpr ⟨j, hj⟩
    have hcard : (insert i (I.erase j)).card ≤ m := by
      rw [Finset.card_insert_of_notMem hi', Finset.card_erase_of_mem hj]
      omega
    have h := hmax _ hcard
    rw [Finset.sum_insert hi', Finset.sum_erase_eq_sub hj] at h
    linarith
  have h2 : I.card < m → w i ^ 2 = 0 := by
    intro hlt
    have hcard : (insert i I).card ≤ m := by
      rw [Finset.card_insert_of_notMem hi]
      omega
    have h := hmax _ hcard
    rw [Finset.sum_insert hi] at h
    have := sq_nonneg (w i)
    linarith
  have h3 : (I.card : ℝ) * w i ^ 2 ≤ ∑ j ∈ I, w j ^ 2 := by
    have : ∑ _j ∈ I, w i ^ 2 = (I.card : ℝ) * w i ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← this]
    exact Finset.sum_le_sum h1
  have h4 : ∑ j ∈ I, w j ^ 2 ≤ ∑ j, w j ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => sq_nonneg _)
  rcases Nat.lt_or_ge I.card m with hlt | hge
  · rw [h2 hlt, mul_zero]
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  · have hIm : I.card = m := le_antisymm hI hge
    rw [← hIm]
    linarith

end Loc

end SparseStack
