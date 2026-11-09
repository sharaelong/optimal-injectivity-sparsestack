import SparseStack.Repair.BlockLaw
import SparseStack.Sketch.Mean

/-!
# Head repair: retention in the two groups (HR3, HR4, HR6) (paper, lines 1031–1085)

Definitions (`retCount`, `badSet`, `goodSet`, `aloneIn`, `blockLaw`, `ofBlocks`) are W-REP's, in
`SparseStack/Repair/Defs.lean`.

* `badSet_subset`, `goodSet_subset`, `disjoint_badSet_goodSet`, `badSet_union_goodSet`,
  `mem_badSet_iff`, `mem_goodSet_iff`: the good/bad split of the head.
* `retained_head_gram`: the retained head Gram is `diag(a_i/s)`; `sqNorm_retain_le`: deleting
  rows does not increase energy.
* `prob_retCount_lt_le` (HR3): a coordinate of the head is retained in a block with probability
  `≥ 15/16`; the retained-incidence count is `1`-Lipschitz in each block, so McDiarmid
  (`mcdiarmid_lower`, deviation `s/48`) gives `P{a_i < a₀ s} ≤ e^{-s/1152}`.
* `prob_badSet_card_le` (HR4): Markov on `|B|`: `P{|B| > N e^{-s/2304}} ≤ e^{-s/2304}`.
* `retention_group2`: if every coordinate of `B` collides in a block with probability
  `≤ |B|/b ≤ π`, the subset bound (failure needs `≥ s/12` collision blocks) and a union bound
  give `P{∃ i ∈ B, a_i < a₀ s} ≤ |B| · 2^s π^{s/12}`.
* `prob_retention2_le` (HR6): the case `π = e^{-s/2304}/16`.

All probabilities are computed on the block product `sketchLaw_prob_ofBlocks` (`BlockLaw.lean`).
-/

namespace SparseStack

open SparseFock

/-! ## The good/bad split -/

theorem mem_badSet_iff {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n) (i : Fin n) :
    i ∈ badSet I ω ↔ i ∈ I ∧ (retCount I ω i : ℝ) < a0 * s :=
  Finset.mem_filter

theorem mem_goodSet_iff {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n) (i : Fin n) :
    i ∈ goodSet I ω ↔ i ∈ I ∧ a0 * s ≤ (retCount I ω i : ℝ) := by
  rw [goodSet, Finset.mem_filter, not_lt]

theorem badSet_subset {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n) :
    badSet I ω ⊆ I :=
  Finset.filter_subset _ _

theorem goodSet_subset {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n) :
    goodSet I ω ⊆ I :=
  Finset.filter_subset _ _

theorem disjoint_badSet_goodSet {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n) :
    Disjoint (badSet I ω) (goodSet I ω) := by
  rw [Finset.disjoint_left]
  intro i hB hG
  rw [mem_badSet_iff] at hB
  rw [mem_goodSet_iff] at hG
  exact absurd hG.2 (not_le.2 hB.2)

theorem badSet_union_goodSet {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n) :
    badSet I ω ∪ goodSet I ω = I := by
  ext i
  rw [Finset.mem_union, mem_badSet_iff, mem_goodSet_iff]
  constructor
  · rintro (h | h)
    · exact h.1
    · exact h.1
  · intro hi
    by_cases h : (retCount I ω i : ℝ) < a0 * s
    · exact Or.inl ⟨hi, h⟩
    · exact Or.inr ⟨hi, not_lt.1 h⟩

/-! ## The retained head Gram -/

private theorem signValue_mul_self'' (β : Bool) : signValue β * signValue β = 1 := by
  cases β <;> norm_num [signValue]

private theorem inv_sqrt_mul_inv_sqrt' (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ = x⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt hx]

/-- Row `p` of `T Π v` is row `p` of `Π v` if the bucket `p` holds exactly one coordinate of `I`,
and `0` otherwise. -/
theorem retain_mulVec_apply {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n)
    (v : Fin n → ℝ) (p : Fin s × Fin b) :
    (retainMatrix I ω * sketchMatrix ω).mulVec v p =
      (if bucketLoad I ω p.1 p.2 = 1 then 1 else 0) * (sketchMatrix ω).mulVec v p := by
  rw [← Matrix.mulVec_mulVec, retainMatrix, Matrix.mulVec_diagonal]

/-- Deleting rows does not increase energy: `‖T Π v‖² ≤ ‖Π v‖²`. -/
theorem sqNorm_retain_le {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n)
    (v : Fin n → ℝ) :
    sqNorm ((retainMatrix I ω * sketchMatrix ω).mulVec v) ≤
      sqNorm ((sketchMatrix ω).mulVec v) := by
  unfold sqNorm dotProduct
  apply Finset.sum_le_sum
  intro p _
  rw [retain_mulVec_apply]
  split_ifs
  · rw [one_mul]
  · rw [zero_mul, zero_mul]
    exact mul_self_nonneg _

/-- In a bucket holding exactly one coordinate `i₀` of `I`, the bucket sum of a vector supported
on `I` is `± h_{i₀}`, so its square is `∑_{i ∈ I, h_t(i) = u} h_i²`. -/
theorem sketchBucketSum_sq_of_load_one {s b n : ℕ} (I : Finset (Fin n))
    (ω : SketchSample s b n) (h : Fin n → ℝ) (hh : ∀ i, i ∉ I → h i = 0) (t : Fin s)
    (u : Fin b) (hload : bucketLoad I ω t u = 1) :
    sketchBucketSum ω h t u ^ 2 = ∑ i ∈ I, (if ω.1 t i = u then h i ^ 2 else 0) := by
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.1 hload
  have hfilter : ∀ g : Fin n → ℝ, ∑ i ∈ I, (if ω.1 t i = u then g i else 0) = g i₀ := by
    intro g
    rw [← Finset.sum_filter]
    have hi₀' : I.filter (fun i => ω.1 t i = u) = {i₀} := hi₀
    rw [hi₀', Finset.sum_singleton]
  have hsupp : sketchBucketSum ω h t u =
      ∑ i ∈ I, (if ω.1 t i = u then signValue (ω.2 t i) else 0) * h i := by
    unfold sketchBucketSum
    symm
    apply Finset.sum_subset (Finset.subset_univ I)
    intro i _ hi
    rw [hh i hi, mul_zero]
  have hsum1 : sketchBucketSum ω h t u = signValue (ω.2 t i₀) * h i₀ := by
    rw [hsupp]
    simp only [ite_mul, zero_mul]
    exact hfilter (fun i => signValue (ω.2 t i) * h i)
  rw [hsum1, hfilter (fun i => h i ^ 2)]
  calc (signValue (ω.2 t i₀) * h i₀) ^ 2
      = (signValue (ω.2 t i₀) * signValue (ω.2 t i₀)) * h i₀ ^ 2 := by ring
    _ = h i₀ ^ 2 := by rw [signValue_mul_self'', one_mul]

/-- Retained head Gram is `diag(a_i/s)`: for `h` supported on `I`,
`‖T Π h‖² = ∑_{i∈I} (a_i/s) h_i²`. -/
theorem retained_head_gram {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n)
    (h : Fin n → ℝ) (hh : ∀ i, i ∉ I → h i = 0) :
    sqNorm ((retainMatrix I ω * sketchMatrix ω).mulVec h) =
      ∑ i ∈ I, (retCount I ω i : ℝ) / s * h i ^ 2 := by
  -- `r t u` is the retention indicator of the row `(t,u)`, `R t i` that of the row of `i`.
  have step1 : sqNorm ((retainMatrix I ω * sketchMatrix ω).mulVec h) =
      ∑ t, ∑ u, (if bucketLoad I ω t u = 1 then (1 : ℝ) else 0) *
        ((s : ℝ)⁻¹ * sketchBucketSum ω h t u ^ 2) := by
    unfold sqNorm dotProduct
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    rw [retain_mulVec_apply, sketchMatrix_mulVec_apply]
    dsimp only
    split_ifs
    · rw [← inv_sqrt_mul_inv_sqrt' _ (Nat.cast_nonneg s)]
      ring
    · ring
  have step2 : ∀ t u, (if bucketLoad I ω t u = 1 then (1 : ℝ) else 0) *
      ((s : ℝ)⁻¹ * sketchBucketSum ω h t u ^ 2) =
      ∑ i ∈ I, (s : ℝ)⁻¹ * (if ω.1 t i = u then
        (if bucketLoad I ω t (ω.1 t i) = 1 then (1 : ℝ) else 0) * h i ^ 2 else 0) := by
    intro t u
    by_cases hload : bucketLoad I ω t u = 1
    · rw [if_pos hload, one_mul, sketchBucketSum_sq_of_load_one I ω h hh t u hload,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hiu : ω.1 t i = u
      · rw [if_pos hiu, if_pos hiu, hiu, if_pos hload, one_mul]
      · rw [if_neg hiu, if_neg hiu]
    · rw [if_neg hload, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro i _
      by_cases hiu : ω.1 t i = u
      · rw [if_pos hiu, hiu, if_neg hload, zero_mul, mul_zero]
      · rw [if_neg hiu, mul_zero]
  have step3 : ∀ t, ∑ u, ∑ i ∈ I, (s : ℝ)⁻¹ * (if ω.1 t i = u then
      (if bucketLoad I ω t (ω.1 t i) = 1 then (1 : ℝ) else 0) * h i ^ 2 else 0) =
      ∑ i ∈ I, (s : ℝ)⁻¹ *
        ((if bucketLoad I ω t (ω.1 t i) = 1 then (1 : ℝ) else 0) * h i ^ 2) := by
    intro t
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  calc sqNorm ((retainMatrix I ω * sketchMatrix ω).mulVec h)
      = ∑ t, ∑ u, ∑ i ∈ I, (s : ℝ)⁻¹ * (if ω.1 t i = u then
          (if bucketLoad I ω t (ω.1 t i) = 1 then (1 : ℝ) else 0) * h i ^ 2 else 0) := by
        rw [step1]
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro u _
        exact step2 t u
    _ = ∑ t, ∑ i ∈ I, (s : ℝ)⁻¹ *
          ((if bucketLoad I ω t (ω.1 t i) = 1 then (1 : ℝ) else 0) * h i ^ 2) :=
        Finset.sum_congr rfl (fun t _ => step3 t)
    _ = ∑ i ∈ I, ∑ t, (s : ℝ)⁻¹ *
          ((if bucketLoad I ω t (ω.1 t i) = 1 then (1 : ℝ) else 0) * h i ^ 2) :=
        Finset.sum_comm
    _ = ∑ i ∈ I, (retCount I ω i : ℝ) / s * h i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_boole, retCount]
        ring

/-! ## Retention probabilities -/

/-- HR3: `P{a_i < a₀ s} ≤ e^{-s/1152}` for every head coordinate `i ∈ I`, when `16|I| ≤ b`. -/
theorem prob_retCount_lt_le {s b n : ℕ} (hb : 0 < b) (hs : 1 ≤ s) (I : Finset (Fin n))
    (hIb : 16 * I.card ≤ b) {i : Fin n} (hi : i ∈ I) :
    (sketchLaw s b n hb).prob {ω | (retCount I ω i : ℝ) < a0 * s} ≤
      Real.exp (-(s : ℝ) / 1152) := by
  classical
  have hs' : (0 : ℝ) < s := Nat.cast_pos.2 hs
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  rw [sketchLaw_prob_ofBlocks]
  set μ : Fin s → FiniteLaw (BlockSample b n) := fun _ => blockLaw b n hb with hμ
  set g : BlockSample b n → ℝ := fun y => if aloneIn I i y then 1 else 0 with hg
  set F : (Fin s → BlockSample b n) → ℝ := fun x => ∑ t, g (x t) with hF
  have hg01 : ∀ y, 0 ≤ g y ∧ g y ≤ 1 := by
    intro y
    simp only [hg]
    split_ifs <;> norm_num
  -- the retained count in block form
  have hret : ∀ x : Fin s → BlockSample b n, (retCount I (ofBlocks x) i : ℝ) = F x := by
    intro x
    have hfilt : Finset.univ.filter
        (fun t : Fin s => bucketLoad I (ofBlocks x) t ((ofBlocks x).1 t i) = 1) =
        Finset.univ.filter (fun t => aloneIn I i (x t)) := by
      apply Finset.filter_congr
      intro t _
      exact bucketLoad_eq_one_iff I (ofBlocks x) t hi
    rw [retCount, hfilt, hF]
    simp only [hg]
    rw [Finset.sum_boole]
  -- one block: `P{i alone} ≥ 15/16`
  have hEg : (15 / 16 : ℝ) ≤ (blockLaw b n hb).expect g := by
    have h1 : (blockLaw b n hb).expect g = (blockLaw b n hb).prob {y | aloneIn I i y} := by
      rw [FiniteLaw.prob]
      apply FiniteLaw.expect_congr
      intro y
      by_cases hy : aloneIn I i y
      · rw [indicator_of_mem (show y ∈ {y | aloneIn I i y} from hy)]
        simp only [hg, if_pos hy]
      · rw [indicator_of_notMem (show y ∉ {y | aloneIn I i y} from hy)]
        simp only [hg, if_neg hy]
    have h2 := FiniteLaw.prob_compl (blockLaw b n hb) {y | aloneIn I i y}
    rw [Set.compl_ofPred] at h2
    have h3 := blockLaw_prob_not_alone_le hb I i
    have h4 : (I.card : ℝ) / b ≤ 1 / 16 := by
      rw [div_le_iff₀ hb']
      have : (16 * I.card : ℝ) ≤ b := by exact_mod_cast hIb
      linarith
    rw [h1]
    linarith
  -- `E F ≥ (15/16) s`
  have hEF : (15 / 16 : ℝ) * s ≤ (FiniteLaw.independentProduct μ).expect F := by
    have h1 : (FiniteLaw.independentProduct μ).expect F =
        ∑ t : Fin s, (FiniteLaw.independentProduct μ).expect (fun x => g (x t)) :=
      expect_sum (FiniteLaw.independentProduct μ) Finset.univ
        (fun (t : Fin s) (x : Fin s → BlockSample b n) => g (x t))
    have h2 : ∀ t : Fin s, (FiniteLaw.independentProduct μ).expect (fun x => g (x t)) =
        (blockLaw b n hb).expect g :=
      fun t => FiniteLaw.expect_independentProduct_apply μ t g
    rw [h1, Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    nlinarith [hEg, (Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  -- bounded differences: changing one block changes `F` by at most `1`
  have hbd : ∀ (x : Fin s → BlockSample b n) (t : Fin s) (a : BlockSample b n),
      |F (Function.update x t a) - F x| ≤ (fun _ => (1 : ℝ)) t := by
    intro x t a
    have h1 : F (Function.update x t a) = g a + ∑ t' ∈ Finset.univ.erase t, g (x t') := by
      simp only [hF]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t), Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro t' ht'
      rw [Function.update_of_ne (Finset.ne_of_mem_erase ht')]
    have h2 : F x = g (x t) + ∑ t' ∈ Finset.univ.erase t, g (x t') := by
      simp only [hF]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
    rw [h1, h2, abs_le]
    obtain ⟨ha0, ha1⟩ := hg01 a
    obtain ⟨hx0, hx1⟩ := hg01 (x t)
    constructor <;> linarith
  have hmc := mcdiarmid_lower μ F (fun _ => (1 : ℝ)) hbd (t := (s : ℝ) / 48)
    (div_pos hs' (by norm_num))
  calc (FiniteLaw.independentProduct μ).prob {x | (retCount I (ofBlocks x) i : ℝ) < a0 * s}
      ≤ (FiniteLaw.independentProduct μ).prob
          {x | F x ≤ (FiniteLaw.independentProduct μ).expect F - (s : ℝ) / 48} := by
        apply prob_le_of_subset
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [hret x] at hx
        have : a0 * (s : ℝ) ≤ (FiniteLaw.independentProduct μ).expect F - (s : ℝ) / 48 := by
          simp only [a0]
          linarith
        linarith
    _ ≤ Real.exp (-2 * ((s : ℝ) / 48) ^ 2 / ∑ _t : Fin s, (fun _ => (1 : ℝ)) _t ^ 2) := hmc
    _ = Real.exp (-(s : ℝ) / 1152) := by
        congr 1
        simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one]
        field_simp
        ring

/-- HR4: `P{|B| > N e^{-s/2304}} ≤ e^{-s/2304}` (Markov on `|B|`). -/
theorem prob_badSet_card_le {s b n : ℕ} (hb : 0 < b) (hs : 1 ≤ s) (I : Finset (Fin n))
    (hIb : 16 * I.card ≤ b) :
    (sketchLaw s b n hb).prob
        {ω | (I.card : ℝ) * Real.exp (-(s : ℝ) / 2304) < (badSet I ω).card} ≤
      Real.exp (-(s : ℝ) / 2304) := by
  classical
  have hsq : Real.exp (-(s : ℝ) / 1152) =
      Real.exp (-(s : ℝ) / 2304) * Real.exp (-(s : ℝ) / 2304) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he : 0 < Real.exp (-(s : ℝ) / 2304) := Real.exp_pos _
  -- `|B|` is a sum of indicators
  have hcard : ∀ ω : SketchSample s b n, ((badSet I ω).card : ℝ) =
      ∑ j ∈ I, FiniteLaw.indicator {ω | (retCount I ω j : ℝ) < a0 * s} ω := by
    intro ω
    rw [badSet, Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : (retCount I ω j : ℝ) < a0 * s
    · rw [if_pos h, indicator_of_mem (show ω ∈ {ω | (retCount I ω j : ℝ) < a0 * s} from h)]
    · rw [if_neg h, indicator_of_notMem (show ω ∉ {ω | (retCount I ω j : ℝ) < a0 * s} from h)]
  -- `E|B| ≤ N e^{-s/1152}`
  have hE : (sketchLaw s b n hb).expect (fun ω => ((badSet I ω).card : ℝ)) ≤
      I.card * Real.exp (-(s : ℝ) / 1152) := by
    rw [FiniteLaw.expect_congr _ hcard, expect_sum]
    calc ∑ j ∈ I, (sketchLaw s b n hb).expect
          (FiniteLaw.indicator {ω | (retCount I ω j : ℝ) < a0 * s})
        ≤ ∑ _j ∈ I, Real.exp (-(s : ℝ) / 1152) :=
          Finset.sum_le_sum (fun j hj => prob_retCount_lt_le hb hs I hIb hj)
      _ = I.card * Real.exp (-(s : ℝ) / 1152) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos I.card with hN | hN
  · -- `I = ∅`: the event is empty
    have hempty : {ω : SketchSample s b n |
        (I.card : ℝ) * Real.exp (-(s : ℝ) / 2304) < (badSet I ω).card} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have h1 : (badSet I ω).card ≤ I.card := Finset.card_le_card (badSet_subset I ω)
      rw [hN] at h1 ⊢
      have h2 : (badSet I ω).card = 0 := by omega
      rw [h2]
      simp
    rw [hempty, FiniteLaw.prob_empty]
    exact he.le
  · have hthr : 0 < (I.card : ℝ) * Real.exp (-(s : ℝ) / 2304) := by
      have : (0 : ℝ) < I.card := by exact_mod_cast hN
      positivity
    have hlt_le : {ω : SketchSample s b n |
        (I.card : ℝ) * Real.exp (-(s : ℝ) / 2304) < (badSet I ω).card} ⊆
        {ω | (I.card : ℝ) * Real.exp (-(s : ℝ) / 2304) ≤ (badSet I ω).card} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      exact le_of_lt hω
    calc (sketchLaw s b n hb).prob
          {ω | (I.card : ℝ) * Real.exp (-(s : ℝ) / 2304) < (badSet I ω).card}
        ≤ (sketchLaw s b n hb).prob
          {ω | (I.card : ℝ) * Real.exp (-(s : ℝ) / 2304) ≤ (badSet I ω).card} :=
          FiniteLaw.prob_mono _ hlt_le
      _ ≤ (sketchLaw s b n hb).expect (fun ω => ((badSet I ω).card : ℝ)) /
            ((I.card : ℝ) * Real.exp (-(s : ℝ) / 2304)) :=
          FiniteLaw.markov _ (f := fun ω => ((badSet I ω).card : ℝ))
            (fun ω => Nat.cast_nonneg _) hthr
      _ ≤ (I.card * Real.exp (-(s : ℝ) / 1152)) /
            ((I.card : ℝ) * Real.exp (-(s : ℝ) / 2304)) :=
          div_le_div_of_nonneg_right hE hthr.le
      _ = Real.exp (-(s : ℝ) / 2304) := by
          rw [hsq]
          field_simp

/-- Counting step of group 2, insensitive to the decidability instance of the complementary
predicate `q`: if fewer than `c` indices satisfy `p` then at least `#κ - c` satisfy `q = ¬p`. -/
private theorem le_card_filter_of_compl {κ : Type*} [Fintype κ] (p q : κ → Prop)
    [DecidablePred p] {instq : DecidablePred q} (hpq : ∀ t, q t ↔ ¬ p t) {c u : ℝ}
    (hc : ((Finset.univ.filter p).card : ℝ) < c) (hu : u ≤ (Fintype.card κ : ℝ) - c) :
    u ≤ ((@Finset.filter κ q instq Finset.univ).card : ℝ) := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset κ)) p
  have hq : @Finset.filter κ q instq Finset.univ = Finset.univ.filter (fun t => ¬ p t) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpq]
  rw [hq]
  rw [Finset.card_univ] at hsplit
  have hcast : ((Finset.univ.filter p).card : ℝ) +
      ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ) = Fintype.card κ := by
    exact_mod_cast hsplit
  linarith

/-- Group-2 retention (lines 1056–1078): if the per-block collision probability bound `π`
satisfies `|B| ≤ π b`, `0 ≤ π ≤ 1`, then `P{∃ i ∈ B, a_i < a₀ s} ≤ |B| · 2^s π^{s/12}`. -/
theorem retention_group2 {s b n : ℕ} (hb : 0 < b) (B : Finset (Fin n)) {π : ℝ} (hπ0 : 0 ≤ π)
    (hπ1 : π ≤ 1) (hπ : (B.card : ℝ) ≤ π * b) :
    (sketchLaw s b n hb).prob {ω | ∃ i ∈ B, (retCount B ω i : ℝ) < a0 * s} ≤
      (B.card : ℝ) * (2 ^ s * π ^ ((s : ℝ) / 12)) := by
  classical
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  -- one coordinate: the subset bound on the collision blocks
  have hone : ∀ i ∈ B, (sketchLaw s b n hb).prob {ω | (retCount B ω i : ℝ) < a0 * s} ≤
      2 ^ s * π ^ ((s : ℝ) / 12) := by
    intro i hi
    rw [sketchLaw_prob_ofBlocks]
    set μ : Fin s → FiniteLaw (BlockSample b n) := fun _ => blockLaw b n hb with hμ
    set E : Fin s → Set (Fin s → BlockSample b n) := fun t => {x | ¬ aloneIn B i (x t)} with hE
    have hS : Pairwise (fun j k : Fin s => Disjoint ({j} : Finset (Fin s)) {k}) :=
      fun j k hjk => Finset.disjoint_singleton.2 hjk
    have hEdep : ∀ (t : Fin s) (x y : Fin s → BlockSample b n),
        (∀ t' ∈ ({t} : Finset (Fin s)), x t' = y t') → (x ∈ E t ↔ y ∈ E t) := by
      intro t x y hxy
      have hxyt : x t = y t := hxy t (Finset.mem_singleton_self t)
      simp only [hE, Set.mem_ofPred_eq, hxyt]
    have hπE : ∀ t, (FiniteLaw.independentProduct μ).prob (E t) ≤ π := by
      intro t
      have h1 : (FiniteLaw.independentProduct μ).prob (E t) =
          (blockLaw b n hb).prob {y | ¬ aloneIn B i y} :=
        FiniteLaw.prob_independentProduct_apply μ t {y | ¬ aloneIn B i y}
      rw [h1]
      refine (blockLaw_prob_not_alone_le hb B i).trans ?_
      rw [div_le_iff₀ hb']
      exact hπ
    have hsb := subset_bound μ (fun t => ({t} : Finset (Fin s))) hS E hEdep hπ0 hπ1 hπE
      (u := (s : ℝ) / 12) (by positivity)
    rw [Fintype.card_fin] at hsb
    refine (prob_le_of_subset _ ?_).trans hsb
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hret : retCount B (ofBlocks x) i =
        (Finset.univ.filter (fun t => aloneIn B i (x t))).card := by
      unfold retCount
      congr 1
      apply Finset.filter_congr
      intro t _
      exact bucketLoad_eq_one_iff B (ofBlocks x) t hi
    rw [hret] at hx
    refine le_card_filter_of_compl (fun t => aloneIn B i (x t)) _ (fun t => Iff.rfl) hx ?_
    rw [Fintype.card_fin]
    simp only [a0]
    linarith
  -- union bound over the head
  have hU : {ω : SketchSample s b n | ∃ i ∈ B, (retCount B ω i : ℝ) < a0 * s} =
      ⋃ i ∈ B, {ω : SketchSample s b n | (retCount B ω i : ℝ) < a0 * s} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [hU]
  calc (sketchLaw s b n hb).prob
        (⋃ i ∈ B, {ω : SketchSample s b n | (retCount B ω i : ℝ) < a0 * s})
      ≤ ∑ i ∈ B, (sketchLaw s b n hb).prob {ω | (retCount B ω i : ℝ) < a0 * s} :=
        prob_union_le_sum _ _ _
    _ ≤ ∑ _i ∈ B, (2 ^ s * π ^ ((s : ℝ) / 12)) := Finset.sum_le_sum hone
    _ = (B.card : ℝ) * (2 ^ s * π ^ ((s : ℝ) / 12)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- HR6: for a fixed head `B` with `16 |B| ≤ b e^{-s/2304}`,
`P{∃ i ∈ B, a_i < a₀ s} ≤ |B| · 2^s (e^{-s/2304}/16)^{s/12}`. -/
theorem prob_retention2_le {s b n : ℕ} (hb : 0 < b) (hs : 1 ≤ s) (B : Finset (Fin n))
    (hB : 16 * (B.card : ℝ) ≤ b * Real.exp (-(s : ℝ) / 2304)) :
    (sketchLaw s b n hb).prob {ω | ∃ i ∈ B, (retCount B ω i : ℝ) < a0 * s} ≤
      B.card * ((2 : ℝ) ^ s * (Real.exp (-(s : ℝ) / 2304) / 16) ^ ((s : ℝ) / 12)) := by
  have he0 : 0 ≤ Real.exp (-(s : ℝ) / 2304) := (Real.exp_pos _).le
  have he1 : Real.exp (-(s : ℝ) / 2304) ≤ 1 := by
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    calc Real.exp (-(s : ℝ) / 2304) ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have hπ : (B.card : ℝ) ≤ Real.exp (-(s : ℝ) / 2304) / 16 * b := by linarith
  exact retention_group2 hb B (by positivity) (by linarith) hπ

end SparseStack
