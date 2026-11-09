import SparseStack.Prob.Basic

/-!
# Resampling coordinates of an independent product; disjoint blocks (contract 4)

For `P = independentProduct μ` and a finite set `s` of coordinates, `s.piecewise z y` takes the
coordinates in `s` from `z` and the others from `y`. The basic identity is the *resampling
identity* `expect_expect_piecewise`: if `y, z` are independent with law `P`, then
`s.piecewise z y` again has law `P`. (Proof: the involution
`(y, z) ↦ (s.piecewise z y, s.piecewise y z)` preserves the product weight `P y * P z`.)
From it we get
* the partial-expectation operator `resampleAvg μ s F x = E_y F (s.piecewise y x)` (averaging out
  the coordinates in `s`), its tower property and bounded-difference stability (used for
  McDiarmid's inequality);
* independence of observables depending on disjoint sets of coordinates, and hence the block
  factorization `expect_prod_disjoint_blocks` (contract 4).
-/

open scoped BigOperators

namespace SparseStack

open SparseFock

noncomputable section

section Resample

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- The product weight is invariant under swapping the coordinates in `s` between two points. -/
theorem independentProduct_weight_piecewise_mul (μ : ι → FiniteLaw α) (s : Finset ι)
    (y z : ι → α) :
    (FiniteLaw.independentProduct μ).weight (s.piecewise z y) *
        (FiniteLaw.independentProduct μ).weight (s.piecewise y z) =
      (FiniteLaw.independentProduct μ).weight y * (FiniteLaw.independentProduct μ).weight z := by
  simp only [FiniteLaw.independentProduct_weight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ s
  · rw [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ hi, mul_comm]
  · rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_notMem _ _ _ hi]

/-- **Resampling identity**: resampling the coordinates in `s` from an independent copy does not
change the law of an independent product. -/
theorem expect_expect_piecewise (μ : ι → FiniteLaw α) (s : Finset ι) (G : (ι → α) → ℝ) :
    (FiniteLaw.independentProduct μ).expect (fun y =>
      (FiniteLaw.independentProduct μ).expect (fun z => G (s.piecewise z y))) =
      (FiniteLaw.independentProduct μ).expect G := by
  set P := FiniteLaw.independentProduct μ with hP
  let Φ : (ι → α) × (ι → α) → (ι → α) × (ι → α) :=
    fun p => (s.piecewise p.2 p.1, s.piecewise p.1 p.2)
  have hΦ : Function.Involutive Φ := by
    intro p
    ext i
    · by_cases hi : i ∈ s
      · simp [Φ, Finset.piecewise_eq_of_mem _ _ _ hi]
      · simp [Φ, Finset.piecewise_eq_of_notMem _ _ _ hi]
    · by_cases hi : i ∈ s
      · simp [Φ, Finset.piecewise_eq_of_mem _ _ _ hi]
      · simp [Φ, Finset.piecewise_eq_of_notMem _ _ _ hi]
  have hsum : ∀ y : ι → α, ∑ z, P.weight y * P.weight z * G y = P.weight y * G y := by
    intro y
    rw [← Finset.sum_mul, ← Finset.mul_sum, P.sum_weight]
    ring
  calc P.expect (fun y => P.expect (fun z => G (s.piecewise z y)))
      = ∑ p : (ι → α) × (ι → α), P.weight p.1 * P.weight p.2 * G (s.piecewise p.2 p.1) := by
        rw [Fintype.sum_prod_type]
        simp only [FiniteLaw.expect, Finset.mul_sum, mul_assoc]
    _ = ∑ p : (ι → α) × (ι → α), P.weight (Φ p).1 * P.weight (Φ p).2 * G (Φ p).1 := by
        apply Finset.sum_congr rfl
        intro p _
        simp only [Φ]
        rw [hP, independentProduct_weight_piecewise_mul μ s p.1 p.2]
    _ = ∑ p : (ι → α) × (ι → α), P.weight p.1 * P.weight p.2 * G p.1 :=
        Equiv.sum_comp (Function.Involutive.toPerm Φ hΦ)
          (fun p => P.weight p.1 * P.weight p.2 * G p.1)
    _ = P.expect G := by
        rw [Fintype.sum_prod_type]
        simp only [hsum]
        rfl

/-- Observables depending on disjoint sets of coordinates (`A` and its complement) are
independent. -/
theorem expect_mul_of_dependsOn (μ : ι → FiniteLaw α) (A : Finset ι) (g h : (ι → α) → ℝ)
    (hg : ∀ x y, (∀ i ∈ A, x i = y i) → g x = g y)
    (hh : ∀ x y, (∀ i, i ∉ A → x i = y i) → h x = h y) :
    (FiniteLaw.independentProduct μ).expect (fun x => g x * h x) =
      (FiniteLaw.independentProduct μ).expect g * (FiniteLaw.independentProduct μ).expect h := by
  set P := FiniteLaw.independentProduct μ
  have h1 : ∀ y z : ι → α, g (A.piecewise z y) = g z := fun y z =>
    hg _ _ (fun i hi => Finset.piecewise_eq_of_mem _ _ _ hi)
  have h2 : ∀ y z : ι → α, h (A.piecewise z y) = h y := fun y z =>
    hh _ _ (fun i hi => Finset.piecewise_eq_of_notMem _ _ _ hi)
  rw [← expect_expect_piecewise μ A (fun x => g x * h x)]
  calc P.expect (fun y => P.expect (fun z => g (A.piecewise z y) * h (A.piecewise z y)))
      = P.expect (fun y => P.expect g * h y) := by
        apply P.expect_congr
        intro y
        simp only [h1, h2]
        exact expect_mul_const P g (h y)
    _ = P.expect g * P.expect h := FiniteLaw.expect_smul P _ h

/-! ### Partial averages -/

/-- Average out the coordinates in `s`: `resampleAvg μ s F x = E_y F (s.piecewise y x)`, the
conditional expectation of `F` given the coordinates outside `s`. -/
def resampleAvg (μ : ι → FiniteLaw α) (s : Finset ι) (F : (ι → α) → ℝ) (x : ι → α) : ℝ :=
  (FiniteLaw.independentProduct μ).expect (fun y => F (s.piecewise y x))

theorem resampleAvg_empty (μ : ι → FiniteLaw α) (F : (ι → α) → ℝ) :
    resampleAvg μ ∅ F = F := by
  funext x
  simp [resampleAvg]

theorem resampleAvg_univ (μ : ι → FiniteLaw α) (F : (ι → α) → ℝ) (x : ι → α) :
    resampleAvg μ Finset.univ F x = (FiniteLaw.independentProduct μ).expect F := by
  simp [resampleAvg]

/-- Averaging out preserves expectations (tower property with the trivial σ-algebra). -/
theorem expect_resampleAvg (μ : ι → FiniteLaw α) (s : Finset ι) (F : (ι → α) → ℝ) :
    (FiniteLaw.independentProduct μ).expect (resampleAvg μ s F) =
      (FiniteLaw.independentProduct μ).expect F :=
  expect_expect_piecewise μ s F

/-- Tower property of partial averages. -/
theorem resampleAvg_resampleAvg (μ : ι → FiniteLaw α) (s t : Finset ι) (F : (ι → α) → ℝ) :
    resampleAvg μ s (resampleAvg μ t F) = resampleAvg μ (s ∪ t) F := by
  funext x
  simp only [resampleAvg]
  have hpw : ∀ y z : ι → α,
      t.piecewise z (s.piecewise y x) = (s ∪ t).piecewise (t.piecewise z y) x := by
    intro y z
    funext i
    by_cases hit : i ∈ t
    · have hst : i ∈ s ∪ t := Finset.mem_union_right s hit
      rw [Finset.piecewise_eq_of_mem _ _ _ hit, Finset.piecewise_eq_of_mem _ _ _ hst,
        Finset.piecewise_eq_of_mem _ _ _ hit]
    · by_cases his : i ∈ s
      · have hst : i ∈ s ∪ t := Finset.mem_union_left t his
        rw [Finset.piecewise_eq_of_notMem _ _ _ hit, Finset.piecewise_eq_of_mem _ _ _ his,
          Finset.piecewise_eq_of_mem _ _ _ hst, Finset.piecewise_eq_of_notMem _ _ _ hit]
      · have hst : i ∉ s ∪ t := by
          rw [Finset.mem_union]
          exact fun h => h.elim his hit
        rw [Finset.piecewise_eq_of_notMem _ _ _ hit, Finset.piecewise_eq_of_notMem _ _ _ his,
          Finset.piecewise_eq_of_notMem _ _ _ hst]
  simp only [hpw]
  exact expect_expect_piecewise μ t (fun w => F ((s ∪ t).piecewise w x))

/-- A partial average does not depend on the averaged-out coordinates. -/
theorem resampleAvg_piecewise (μ : ι → FiniteLaw α) (s : Finset ι) (F : (ι → α) → ℝ)
    (x y : ι → α) : resampleAvg μ s F (s.piecewise y x) = resampleAvg μ s F x := by
  simp only [resampleAvg]
  apply FiniteLaw.expect_congr
  intro z
  congr 1
  funext i
  by_cases hi : i ∈ s
  · rw [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ hi]
  · rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_notMem _ _ _ hi,
      Finset.piecewise_eq_of_notMem _ _ _ hi]

/-- Pull out a factor that does not depend on the averaged-out coordinates. -/
theorem resampleAvg_mul_left (μ : ι → FiniteLaw α) (s : Finset ι) (g h : (ι → α) → ℝ)
    (x : ι → α) (hg : ∀ y, g (s.piecewise y x) = g x) :
    resampleAvg μ s (fun w => g w * h w) x = g x * resampleAvg μ s h x := by
  simp only [resampleAvg, hg]
  exact FiniteLaw.expect_smul _ _ _

/-- Partial averages preserve bounded differences. -/
theorem resampleAvg_update_le (μ : ι → FiniteLaw α) (s : Finset ι) (F : (ι → α) → ℝ)
    (c : ι → ℝ) (hF : ∀ x i a, |F (Function.update x i a) - F x| ≤ c i)
    (x : ι → α) (i : ι) (a : α) :
    |resampleAvg μ s F (Function.update x i a) - resampleAvg μ s F x| ≤ c i := by
  set P := FiniteLaw.independentProduct μ
  simp only [resampleAvg]
  rw [← FiniteLaw.expect_sub]
  refine (FiniteLaw.abs_expect_le_expect_abs _ _).trans ?_
  calc P.expect (fun y => |F (s.piecewise y (Function.update x i a)) - F (s.piecewise y x)|)
      ≤ P.expect (fun _ => c i) := by
        apply P.expect_mono
        intro y
        by_cases hi : i ∈ s
        · have hpw : s.piecewise y (Function.update x i a) = s.piecewise y x := by
            funext j
            by_cases hj : j ∈ s
            · rw [Finset.piecewise_eq_of_mem _ _ _ hj, Finset.piecewise_eq_of_mem _ _ _ hj]
            · have hji : j ≠ i := fun h => hj (h ▸ hi)
              rw [Finset.piecewise_eq_of_notMem _ _ _ hj, Finset.piecewise_eq_of_notMem _ _ _ hj,
                Function.update_of_ne hji]
          rw [hpw, sub_self, abs_zero]
          exact (abs_nonneg _).trans (hF x i a)
        · have hpw : s.piecewise y (Function.update x i a) =
              Function.update (s.piecewise y x) i a := by
            funext j
            by_cases hj : j ∈ s
            · have hji : j ≠ i := fun h => hi (h ▸ hj)
              rw [Finset.piecewise_eq_of_mem _ _ _ hj, Function.update_of_ne hji,
                Finset.piecewise_eq_of_mem _ _ _ hj]
            · by_cases hji : j = i
              · subst hji
                rw [Finset.piecewise_eq_of_notMem _ _ _ hj, Function.update_self,
                  Function.update_self]
              · rw [Finset.piecewise_eq_of_notMem _ _ _ hj, Function.update_of_ne hji,
                  Function.update_of_ne hji, Finset.piecewise_eq_of_notMem _ _ _ hj]
          rw [hpw]
          exact hF _ i a
    _ = c i := FiniteLaw.expect_const _ _

end Resample

/-! ## Disjoint blocks (contract 4) -/

/-- Block factorization over a `Finset` of blocks. -/
theorem expect_prod_disjoint_blocks_finset {ι α κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (μ : ι → FiniteLaw α) (S : κ → Finset ι)
    (hS : Pairwise (fun j k => Disjoint (S j) (S k)))
    (f : κ → (ι → α) → ℝ) (hf : ∀ j x y, (∀ i ∈ S j, x i = y i) → f j x = f j y)
    (K : Finset κ) :
    (FiniteLaw.independentProduct μ).expect (fun x => ∏ j ∈ K, f j x) =
      ∏ j ∈ K, (FiniteLaw.independentProduct μ).expect (f j) := by
  classical
  induction K using Finset.induction_on with
  | empty => simp
  | insert k K hk ih =>
    simp only [Finset.prod_insert hk]
    rw [expect_mul_of_dependsOn μ (S k) (f k) (fun x => ∏ j ∈ K, f j x) (hf k), ih]
    intro x y hxy
    apply Finset.prod_congr rfl
    intro j hj
    apply hf j
    intro i hi
    apply hxy
    have hjk : j ≠ k := fun h => hk (h ▸ hj)
    exact Finset.disjoint_left.mp (hS hjk) hi

/-- **Block factorization**: observables depending on pairwise disjoint blocks of coordinates
of an independent product are independent. -/
theorem expect_prod_disjoint_blocks {ι α κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [Fintype κ] (μ : ι → FiniteLaw α) (S : κ → Finset ι)
    (hS : Pairwise (fun j k => Disjoint (S j) (S k)))
    (f : κ → (ι → α) → ℝ) (hf : ∀ j x y, (∀ i ∈ S j, x i = y i) → f j x = f j y) :
    (FiniteLaw.independentProduct μ).expect (fun x => ∏ j, f j x) =
      ∏ j, (FiniteLaw.independentProduct μ).expect (f j) :=
  expect_prod_disjoint_blocks_finset μ S hS f hf Finset.univ

end

end SparseStack
