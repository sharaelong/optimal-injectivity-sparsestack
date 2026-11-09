import SparseStack.Repair.Defs
import SparseStack.Prob.Toolkit

/-!
# Head repair: the sample space as an independent product of blocks

* `sketchLaw_expect_ofBlocks`, `sketchLaw_prob_ofBlocks`: the uniform law on `SketchSample s b n`
  is the image under `ofBlocks` of the independent product of `s` uniform block laws.
* `blockLaw_prob_collide`: two distinct coordinates collide in one block with probability `1/b`
  (bijection `y ↦ (y with y_j := y_i, y_j)` between blocks and collision-blocks × `Fin b`).
* `blockLaw_prob_not_alone_le`: `P{i is not alone among I} ≤ |I|/b` (union bound).
* `bucketLoad_eq_one_iff`: for `i ∈ I`, the bucket of `i` in block `t` has load one iff `i` is alone
  among `I` in block `t`.

Proofs (W-SKETCH): `ofBlocks` is the inverse of `sketchSampleEquivBlocks` (`Prob/Sketch.lean`) and
the product of the constant block weights is the constant sample weight; the collision count uses
the explicit equivalence `collideEquiv`.
-/

namespace SparseStack

open SparseFock

/-- `ofBlocks` is the inverse of `sketchSampleEquivBlocks`. -/
theorem ofBlocks_eq_symm {s b n : ℕ} (x : Fin s → BlockSample b n) :
    ofBlocks x = (sketchSampleEquivBlocks s b n).symm x :=
  rfl

theorem blockLaw_weight {b n : ℕ} (hb : 0 < b) (y : BlockSample b n) :
    (blockLaw b n hb).weight y = 1 / (Fintype.card (BlockSample b n) : ℝ) :=
  rfl

/-- The uniform law on samples is the image of the product of the uniform block laws. -/
theorem sketchLaw_expect_ofBlocks {s b n : ℕ} (hb : 0 < b) (F : SketchSample s b n → ℝ) :
    (sketchLaw s b n hb).expect F =
      (FiniteLaw.independentProduct (fun _ : Fin s => blockLaw b n hb)).expect
        (fun x => F (ofBlocks x)) := by
  have hcard : Fintype.card (SketchSample s b n) = Fintype.card (BlockSample b n) ^ s := by
    rw [Fintype.card_congr (sketchSampleEquivBlocks s b n), Fintype.card_fun, Fintype.card_fin]
  have hw : ∀ x : Fin s → BlockSample b n,
      (FiniteLaw.independentProduct (fun _ : Fin s => blockLaw b n hb)).weight x =
        1 / (Fintype.card (SketchSample s b n) : ℝ) := by
    intro x
    rw [FiniteLaw.independentProduct_weight]
    simp only [blockLaw_weight]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcard]
    push_cast
    rw [one_div_pow]
  have hsum : ∑ x : Fin s → BlockSample b n, F (ofBlocks x) = ∑ ω, F ω :=
    Fintype.sum_equiv (sketchSampleEquivBlocks s b n).symm _ _ (fun _ => rfl)
  rw [sketchLaw_expect_eq_sum]
  unfold FiniteLaw.expect
  simp only [hw]
  rw [← Finset.mul_sum, hsum]
  ring

/-- Event version of `sketchLaw_expect_ofBlocks`. -/
theorem sketchLaw_prob_ofBlocks {s b n : ℕ} (hb : 0 < b) (E : SketchSample s b n → Prop) :
    (sketchLaw s b n hb).prob {ω | E ω} =
      (FiniteLaw.independentProduct (fun _ : Fin s => blockLaw b n hb)).prob
        {x | E (ofBlocks x)} := by
  rw [FiniteLaw.prob, FiniteLaw.prob, sketchLaw_expect_ofBlocks]
  rfl

/-- Probabilities under `blockLaw` are normalized counts. -/
theorem blockLaw_prob_eq {b n : ℕ} (hb : 0 < b) (E : BlockSample b n → Prop)
    [DecidablePred E] :
    (blockLaw b n hb).prob {y | E y} =
      ((Finset.univ.filter E).card : ℝ) / (Fintype.card (BlockSample b n) : ℝ) := by
  unfold FiniteLaw.prob FiniteLaw.expect
  simp only [blockLaw_weight]
  rw [Finset.natCast_card_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : E y
  · rw [if_pos h, indicator_of_mem (show y ∈ {y | E y} from h)]
    ring
  · rw [if_neg h, indicator_of_notMem (show y ∉ {y | E y} from h)]
    ring

/-- Re-hash coordinate `j` onto the bucket of `i`, remembering the old bucket of `j`. -/
def collideEquiv {b n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    BlockSample b n ≃ {y : BlockSample b n // y.1 j = y.1 i} × Fin b where
  toFun y := (⟨(Function.update y.1 j (y.1 i), y.2), by
      simp only [Function.update_self, Function.update_of_ne hij]⟩, y.1 j)
  invFun p := (Function.update p.1.1.1 j p.2, p.1.1.2)
  left_inv y := by
    obtain ⟨h, σ⟩ := y
    show (Function.update (Function.update h j (h i)) j (h j), σ) = (h, σ)
    rw [Function.update_idem, Function.update_eq_self]
  right_inv p := by
    obtain ⟨⟨⟨h, σ⟩, hy⟩, c⟩ := p
    have hy' : h j = h i := hy
    refine Prod.ext (Subtype.ext (Prod.ext ?_ rfl)) ?_
    · show Function.update (Function.update h j c) j (Function.update h j c i) = h
      rw [Function.update_of_ne hij, Function.update_idem, ← hy', Function.update_eq_self]
    · show Function.update h j c j = c
      exact Function.update_self j c h

/-- Two distinct coordinates collide in one block with probability exactly `1/b`. -/
theorem blockLaw_prob_collide {b n : ℕ} (hb : 0 < b) {i j : Fin n} (hij : i ≠ j) :
    (blockLaw b n hb).prob {y | y.1 j = y.1 i} = 1 / b := by
  classical
  have hcard : Fintype.card (BlockSample b n) =
      Fintype.card {y : BlockSample b n // y.1 j = y.1 i} * b := by
    rw [Fintype.card_congr (collideEquiv hij), Fintype.card_prod, Fintype.card_fin]
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc : (Fintype.card {y : BlockSample b n // y.1 j = y.1 i} : ℝ) ≠ 0 := by
    have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
    have h0 : Fintype.card (BlockSample b n) ≠ 0 := Fintype.card_ne_zero
    rw [hcard] at h0
    exact_mod_cast left_ne_zero_of_mul h0
  rw [blockLaw_prob_eq hb, ← Fintype.card_subtype, hcard]
  push_cast
  field_simp

/-- A coordinate fails to be alone among `I` in one block with probability at most `|I|/b`. -/
theorem blockLaw_prob_not_alone_le {b n : ℕ} (hb : 0 < b) (I : Finset (Fin n)) (i : Fin n) :
    (blockLaw b n hb).prob {y | ¬ aloneIn I i y} ≤ (I.card : ℝ) / b := by
  have hsub : {y : BlockSample b n | ¬ aloneIn I i y} ⊆
      ⋃ j ∈ I.erase i, {y : BlockSample b n | y.1 j = y.1 i} := by
    intro y hy
    simp only [Set.mem_ofPred_eq, aloneIn] at hy
    push Not at hy
    obtain ⟨j, hj, hji, hne⟩ := hy
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨j, Finset.mem_erase.2 ⟨hne, hj⟩, hji⟩
  calc (blockLaw b n hb).prob {y | ¬ aloneIn I i y}
      ≤ (blockLaw b n hb).prob (⋃ j ∈ I.erase i, {y : BlockSample b n | y.1 j = y.1 i}) :=
        prob_le_of_subset _ hsub
    _ ≤ ∑ j ∈ I.erase i, (blockLaw b n hb).prob {y : BlockSample b n | y.1 j = y.1 i} :=
        prob_union_le_sum _ _ _
    _ = ∑ _j ∈ I.erase i, (1 / (b : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact blockLaw_prob_collide hb (Ne.symm (Finset.ne_of_mem_erase hj))
    _ = ((I.erase i).card : ℝ) / b := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (I.card : ℝ) / b := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg b)
        exact_mod_cast Finset.card_erase_le

/-- For `i ∈ I`: the bucket of `i` in block `t` contains exactly one coordinate of `I` iff `i` is
alone among `I` in block `t`. -/
theorem bucketLoad_eq_one_iff {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n)
    (t : Fin s) {i : Fin n} (hi : i ∈ I) :
    bucketLoad I ω t (ω.1 t i) = 1 ↔ aloneIn I i (ω.1 t, ω.2 t) := by
  unfold bucketLoad aloneIn
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨a, ha⟩ j hj hji
    have hjmem : j ∈ I.filter (fun j => ω.1 t j = ω.1 t i) := Finset.mem_filter.2 ⟨hj, hji⟩
    have himem : i ∈ I.filter (fun j => ω.1 t j = ω.1 t i) := Finset.mem_filter.2 ⟨hi, rfl⟩
    rw [ha, Finset.mem_singleton] at hjmem himem
    rw [hjmem, himem]
  · intro h
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hji⟩
      exact h j hj hji
    · rintro rfl
      exact ⟨hi, rfl⟩

end SparseStack
