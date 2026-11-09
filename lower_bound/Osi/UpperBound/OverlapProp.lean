import Osi.Spec
import Osi.Prelim.SubspaceSing

/-!
# Section 1.1: SparseStack Satisfies the Overlap Condition (`Proposition_SparseStack_Overlap`)

Proves `Proposition_SparseStack_Overlap`: for every `n : ℕ` and `ζ, b ≥ 1` (`k = ζ b`),
`SparseStack(ζ, b, n)` satisfies Definition 1.2 with `η = 5 ζ⁴ / (2 k)` w.p. `≥ 9/10`
(via pairwise row collision expectation `E[overlapPairCount] ≤ C(n, 2) · C(ζ, 2)² / b² ≤ n² ζ⁴ / (4 k)`
when `ζ ≤ b`, trivial `0 ≤ 5 ζ⁴ / (2 k)` when `ζ = 1`, and direct card bound `C(n, 2) < n² / 2 ≤ η n² / k`
whenever `5 ζ³ ≥ b`!).
-/

namespace Osi.UpperBound

open Osi.Spec

/-- Strictly ordered index pairs `(i, j)` with `i < j` in `Fin m`. -/
private def upperPairs (m : ℕ) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun p => p.1 < p.2)

/-- Twice the number of strictly ordered pairs in `Fin m` is at most `m²`. -/
private lemma two_mul_card_upperPairs_le_sq (m : ℕ) :
    2 * (upperPairs m).card ≤ m ^ 2 := by
  have himg : ((upperPairs m).image Prod.swap).card = (upperPairs m).card :=
    Finset.card_image_of_injOn Prod.swap_injective.injOn
  have hdisj : Disjoint (upperPairs m) ((upperPairs m).image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro p hp hswap
    rcases Finset.mem_image.1 hswap with ⟨q, hq, rfl⟩
    simp only [upperPairs, Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap] at hp hq
    exact lt_asymm hp hq
  have hunion : (upperPairs m ∪ (upperPairs m).image Prod.swap).card ≤ m ^ 2 := by
    calc (upperPairs m ∪ (upperPairs m).image Prod.swap).card
        ≤ (Finset.univ : Finset (Fin m × Fin m)).card := Finset.card_le_univ _
      _ = m * m := by simp [Finset.card_univ]
      _ = m ^ 2 := (sq m).symm
  have hcard := Finset.card_union_of_disjoint hdisj
  omega

/-- Any column `j` in the support of row `i` of `sparseStackOmega ω` has bucket hash
`ω.1 (finProdFinEquiv.symm j).1 i = (finProdFinEquiv.symm j).2`. -/
private lemma hash_eq_of_mem_rowSupport {ζ b n : ℕ} (ω : SketchSample ζ b n)
    {i : Fin n} {j : Fin (ζ * b)} (hj : j ∈ rowSupport (sparseStackOmega ω) i) :
    ω.1 (finProdFinEquiv.symm j).1 i = (finProdFinEquiv.symm j).2 := by
  have hne : sparseStackOmega ω i j ≠ 0 := by
    simpa [rowSupport] using hj
  by_contra h
  apply hne
  unfold sparseStackOmega
  dsimp only
  rw [if_neg h, mul_zero]

/-- If rows `u < v` share at least two support columns in `sparseStackOmega ω`, then some strictly
ordered pair of blocks `t.1 < t.2` has bucket collisions in both `t.1` and `t.2`. -/
private lemma exists_doubleColl_of_mem_overlapPairs {ζ b n : ℕ} (ω : SketchSample ζ b n)
    {uv : Fin n × Fin n} (huv : uv ∈ overlapPairs (sparseStackOmega ω)) :
    uv ∈ upperPairs n ∧
      ∃ t ∈ upperPairs ζ,
        ω.1 t.1 uv.1 = ω.1 t.1 uv.2 ∧ ω.1 t.2 uv.1 = ω.1 t.2 uv.2 := by
  have hmem : uv.1 < uv.2 ∧
      2 ≤ (rowSupport (sparseStackOmega ω) uv.1 ∩
        rowSupport (sparseStackOmega ω) uv.2).card := by
    simpa [overlapPairs] using huv
  refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hmem.1⟩, ?_⟩
  have hlt : 1 < (rowSupport (sparseStackOmega ω) uv.1 ∩
      rowSupport (sparseStackOmega ω) uv.2).card := by
    omega
  rcases Finset.one_lt_card_iff.1 hlt with ⟨j₁, j₂, hj₁, hj₂, hne⟩
  rcases Finset.mem_inter.1 hj₁ with ⟨hj₁u, hj₁v⟩
  rcases Finset.mem_inter.1 hj₂ with ⟨hj₂u, hj₂v⟩
  have h₁u := hash_eq_of_mem_rowSupport ω hj₁u
  have h₁v := hash_eq_of_mem_rowSupport ω hj₁v
  have h₂u := hash_eq_of_mem_rowSupport ω hj₂u
  have h₂v := hash_eq_of_mem_rowSupport ω hj₂v
  have hc₁ : ω.1 (finProdFinEquiv.symm j₁).1 uv.1 = ω.1 (finProdFinEquiv.symm j₁).1 uv.2 :=
    h₁u.trans h₁v.symm
  have hc₂ : ω.1 (finProdFinEquiv.symm j₂).1 uv.1 = ω.1 (finProdFinEquiv.symm j₂).1 uv.2 :=
    h₂u.trans h₂v.symm
  have hblock_ne : (finProdFinEquiv.symm j₁).1 ≠ (finProdFinEquiv.symm j₂).1 := by
    intro heq
    apply hne
    apply finProdFinEquiv.symm.injective
    apply Prod.ext
    · exact heq
    · rw [← h₁u, ← h₂u, heq]
  rcases lt_or_gt_of_ne hblock_ne with hlt_b | hgt_b
  · exact ⟨((finProdFinEquiv.symm j₁).1, (finProdFinEquiv.symm j₂).1),
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt_b⟩, hc₁, hc₂⟩
  · exact ⟨((finProdFinEquiv.symm j₂).1, (finProdFinEquiv.symm j₁).1),
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hgt_b⟩, hc₂, hc₁⟩

/-- Strictly ordered row pairs `(u, v)` (`u < v`) colliding in both blocks `t.1` and `t.2`. -/
private def doubleCollRowPairs {ζ b n : ℕ} (ω : SketchSample ζ b n)
    (t : Fin ζ × Fin ζ) : Finset (Fin n × Fin n) :=
  (upperPairs n).filter (fun uv =>
    ω.1 t.1 uv.1 = ω.1 t.1 uv.2 ∧ ω.1 t.2 uv.1 = ω.1 t.2 uv.2)

private lemma overlapPairCount_le_sum_doubleColl {ζ b n : ℕ} (ω : SketchSample ζ b n) :
    overlapPairCount (sparseStackOmega ω) ≤
      ∑ t ∈ upperPairs ζ, (doubleCollRowPairs ω t).card := by
  have hsub : overlapPairs (sparseStackOmega ω) ⊆
      (upperPairs ζ).biUnion (doubleCollRowPairs ω) := by
    intro uv huv
    rcases exists_doubleColl_of_mem_overlapPairs ω huv with ⟨huv_up, t, ht, hc₁, hc₂⟩
    exact Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_filter.2 ⟨huv_up, hc₁, hc₂⟩⟩
  calc overlapPairCount (sparseStackOmega ω)
      ≤ ((upperPairs ζ).biUnion (doubleCollRowPairs ω)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ t ∈ upperPairs ζ, (doubleCollRowPairs ω t).card :=
        Finset.card_biUnion_le

/-- Overwrite the bucket hashes of row `v` in blocks `t₁` and `t₂` with `c₁` and `c₂`. -/
private def overwritePair {ζ b n : ℕ} (t₁ t₂ : Fin ζ) (v : Fin n)
    (ω : SketchSample ζ b n) (c₁ c₂ : Fin b) : SketchSample ζ b n :=
  (fun t i =>
      if i = v then
        if t = t₁ then c₁ else if t = t₂ then c₂ else ω.1 t i
      else ω.1 t i,
    ω.2)

private lemma overwritePair_ne_v {ζ b n : ℕ} {t₁ t₂ : Fin ζ} {u v : Fin n} (huv : u ≠ v)
    (ω : SketchSample ζ b n) (c₁ c₂ : Fin b) (t : Fin ζ) :
    (overwritePair t₁ t₂ v ω c₁ c₂).1 t u = ω.1 t u := by
  simp [overwritePair, huv]

private lemma overwritePair_t₁_v {ζ b n : ℕ} (t₁ t₂ : Fin ζ) (v : Fin n)
    (ω : SketchSample ζ b n) (c₁ c₂ : Fin b) :
    (overwritePair t₁ t₂ v ω c₁ c₂).1 t₁ v = c₁ := by
  simp [overwritePair]

private lemma overwritePair_t₂_v {ζ b n : ℕ} {t₁ t₂ : Fin ζ} (ht : t₁ ≠ t₂) (v : Fin n)
    (ω : SketchSample ζ b n) (c₁ c₂ : Fin b) :
    (overwritePair t₁ t₂ v ω c₁ c₂).1 t₂ v = c₂ := by
  simp [overwritePair, ht.symm]

private lemma overwritePair_overwritePair {ζ b n : ℕ} (t₁ t₂ : Fin ζ) (v : Fin n)
    (ω : SketchSample ζ b n) (a₁ a₂ c₁ c₂ : Fin b) :
    overwritePair t₁ t₂ v (overwritePair t₁ t₂ v ω a₁ a₂) c₁ c₂ =
      overwritePair t₁ t₂ v ω c₁ c₂ := by
  apply Prod.ext
  · funext t i
    by_cases hi : i = v
    · subst hi
      by_cases h₁ : t = t₁
      · simp [overwritePair, h₁]
      · by_cases h₂ : t = t₂
        · simp [overwritePair, h₂]
        · simp [overwritePair, h₁, h₂]
    · simp [overwritePair, hi]
  · rfl

private lemma overwritePair_self {ζ b n : ℕ} (t₁ t₂ : Fin ζ) (v : Fin n)
    (ω : SketchSample ζ b n) :
    overwritePair t₁ t₂ v ω (ω.1 t₁ v) (ω.1 t₂ v) = ω := by
  apply Prod.ext
  · funext t i
    by_cases hi : i = v
    · subst hi
      by_cases h₁ : t = t₁
      · subst h₁; simp [overwritePair]
      · by_cases h₂ : t = t₂
        · subst h₂; simp [overwritePair, h₁]
        · simp [overwritePair, h₁, h₂]
    · simp [overwritePair, hi]
  · rfl

/-- Fiber decomposition showing that double collisions in distinct blocks `t₁ ≠ t₂` between
distinct rows `u ≠ v` occur on an exact `1 / b²` fraction of `SketchSample ζ b n`. -/
private def doubleCollEquiv {ζ b n : ℕ} {t₁ t₂ : Fin ζ} (ht : t₁ ≠ t₂)
    {u v : Fin n} (huv : u ≠ v) :
    SketchSample ζ b n ≃
      {ω : SketchSample ζ b n // ω.1 t₁ u = ω.1 t₁ v ∧ ω.1 t₂ u = ω.1 t₂ v} ×
        (Fin b × Fin b) where
  toFun ω :=
    (⟨overwritePair t₁ t₂ v ω (ω.1 t₁ u) (ω.1 t₂ u), by
        rw [overwritePair_ne_v huv, overwritePair_t₁_v,
          overwritePair_ne_v huv, overwritePair_t₂_v ht]
        exact ⟨rfl, rfl⟩⟩,
      (ω.1 t₁ v, ω.1 t₂ v))
  invFun p := overwritePair t₁ t₂ v p.1.1 p.2.1 p.2.2
  left_inv ω := by
    dsimp only
    rw [overwritePair_overwritePair, overwritePair_self]
  right_inv := by
    rintro ⟨⟨ω₀, h₁, h₂⟩, ⟨c₁, c₂⟩⟩
    apply Prod.ext
    · apply Subtype.ext
      dsimp only
      rw [overwritePair_ne_v huv, overwritePair_ne_v huv,
        overwritePair_overwritePair, h₁, h₂, overwritePair_self]
    · apply Prod.ext
      · exact overwritePair_t₁_v t₁ t₂ v ω₀ c₁ c₂
      · exact overwritePair_t₂_v ht v ω₀ c₁ c₂

private lemma card_doubleColl_mul_sq {ζ b n : ℕ} {t₁ t₂ : Fin ζ} (ht : t₁ ≠ t₂)
    {u v : Fin n} (huv : u ≠ v) :
    (Finset.univ.filter (fun ω : SketchSample ζ b n =>
        ω.1 t₁ u = ω.1 t₁ v ∧ ω.1 t₂ u = ω.1 t₂ v)).card * b ^ 2 =
      Fintype.card (SketchSample ζ b n) := by
  calc (Finset.univ.filter (fun ω : SketchSample ζ b n =>
          ω.1 t₁ u = ω.1 t₁ v ∧ ω.1 t₂ u = ω.1 t₂ v)).card * b ^ 2
      = Fintype.card {ω : SketchSample ζ b n //
          ω.1 t₁ u = ω.1 t₁ v ∧ ω.1 t₂ u = ω.1 t₂ v} * (b * b) := by
        rw [Fintype.card_subtype, sq]
    _ = Fintype.card ({ω : SketchSample ζ b n //
          ω.1 t₁ u = ω.1 t₁ v ∧ ω.1 t₂ u = ω.1 t₂ v} × (Fin b × Fin b)) := by
        rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    _ = Fintype.card (SketchSample ζ b n) :=
        (Fintype.card_congr (doubleCollEquiv (b := b) ht huv)).symm

private lemma sum_doubleCollRowPairs_card {ζ b n : ℕ} (t : Fin ζ × Fin ζ) :
    ∑ ω : SketchSample ζ b n, (doubleCollRowPairs ω t).card =
      ∑ uv ∈ upperPairs n,
        (Finset.univ.filter (fun ω : SketchSample ζ b n =>
          ω.1 t.1 uv.1 = ω.1 t.1 uv.2 ∧ ω.1 t.2 uv.1 = ω.1 t.2 uv.2)).card := by
  simp only [doubleCollRowPairs, Finset.card_filter]
  exact Finset.sum_comm

private lemma four_mul_sq_mul_sum_overlapPairCount_le (n ζ b : ℕ) :
    4 * b ^ 2 * (∑ ω : SketchSample ζ b n, overlapPairCount (sparseStackOmega ω)) ≤
      ζ ^ 2 * n ^ 2 * Fintype.card (SketchSample ζ b n) := by
  have hsum_le :
      ∑ ω : SketchSample ζ b n, overlapPairCount (sparseStackOmega ω) ≤
        ∑ t ∈ upperPairs ζ, ∑ uv ∈ upperPairs n,
          (Finset.univ.filter (fun ω : SketchSample ζ b n =>
            ω.1 t.1 uv.1 = ω.1 t.1 uv.2 ∧ ω.1 t.2 uv.1 = ω.1 t.2 uv.2)).card := by
    calc ∑ ω : SketchSample ζ b n, overlapPairCount (sparseStackOmega ω)
        ≤ ∑ ω : SketchSample ζ b n, ∑ t ∈ upperPairs ζ, (doubleCollRowPairs ω t).card :=
          Finset.sum_le_sum (fun ω _ => overlapPairCount_le_sum_doubleColl ω)
      _ = ∑ t ∈ upperPairs ζ, ∑ ω : SketchSample ζ b n, (doubleCollRowPairs ω t).card :=
          Finset.sum_comm
      _ = ∑ t ∈ upperPairs ζ, ∑ uv ∈ upperPairs n,
            (Finset.univ.filter (fun ω : SketchSample ζ b n =>
              ω.1 t.1 uv.1 = ω.1 t.1 uv.2 ∧ ω.1 t.2 uv.1 = ω.1 t.2 uv.2)).card :=
          Finset.sum_congr rfl (fun t _ => sum_doubleCollRowPairs_card t)
  have hsum_eq :
      (∑ t ∈ upperPairs ζ, ∑ uv ∈ upperPairs n,
          (Finset.univ.filter (fun ω : SketchSample ζ b n =>
            ω.1 t.1 uv.1 = ω.1 t.1 uv.2 ∧ ω.1 t.2 uv.1 = ω.1 t.2 uv.2)).card) * b ^ 2 =
        (upperPairs ζ).card * (upperPairs n).card * Fintype.card (SketchSample ζ b n) := by
    rw [Finset.sum_mul]
    have hinner : ∀ t ∈ upperPairs ζ,
        (∑ uv ∈ upperPairs n,
          (Finset.univ.filter (fun ω : SketchSample ζ b n =>
            ω.1 t.1 uv.1 = ω.1 t.1 uv.2 ∧ ω.1 t.2 uv.1 = ω.1 t.2 uv.2)).card) * b ^ 2 =
          (upperPairs n).card * Fintype.card (SketchSample ζ b n) := by
      intro t ht
      have ht_ne : t.1 ≠ t.2 := ne_of_lt (Finset.mem_filter.1 ht).2
      rw [Finset.sum_mul]
      have huv_eq : ∀ uv ∈ upperPairs n,
          (Finset.univ.filter (fun ω : SketchSample ζ b n =>
            ω.1 t.1 uv.1 = ω.1 t.1 uv.2 ∧ ω.1 t.2 uv.1 = ω.1 t.2 uv.2)).card * b ^ 2 =
            Fintype.card (SketchSample ζ b n) := by
        intro uv huv
        exact card_doubleColl_mul_sq ht_ne (ne_of_lt (Finset.mem_filter.1 huv).2)
      rw [Finset.sum_congr rfl huv_eq, Finset.sum_const, Nat.nsmul_eq_mul]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Nat.nsmul_eq_mul, mul_assoc]
  have hpairs : 4 * ((upperPairs ζ).card * (upperPairs n).card) ≤ ζ ^ 2 * n ^ 2 := by
    calc 4 * ((upperPairs ζ).card * (upperPairs n).card)
        = (2 * (upperPairs ζ).card) * (2 * (upperPairs n).card) := by ring
      _ ≤ ζ ^ 2 * n ^ 2 :=
          Nat.mul_le_mul (two_mul_card_upperPairs_le_sq ζ) (two_mul_card_upperPairs_le_sq n)
  calc 4 * b ^ 2 * (∑ ω : SketchSample ζ b n, overlapPairCount (sparseStackOmega ω))
      = 4 * ((∑ ω : SketchSample ζ b n, overlapPairCount (sparseStackOmega ω)) * b ^ 2) := by
        ring
    _ ≤ 4 * ((∑ t ∈ upperPairs ζ, ∑ uv ∈ upperPairs n,
          (Finset.univ.filter (fun ω : SketchSample ζ b n =>
            ω.1 t.1 uv.1 = ω.1 t.1 uv.2 ∧ ω.1 t.2 uv.1 = ω.1 t.2 uv.2)).card) * b ^ 2) :=
        Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right (b ^ 2) hsum_le)
    _ = 4 * ((upperPairs ζ).card * (upperPairs n).card) *
          Fintype.card (SketchSample ζ b n) := by
        rw [hsum_eq]; ring
    _ ≤ ζ ^ 2 * n ^ 2 * Fintype.card (SketchSample ζ b n) :=
        Nat.mul_le_mul_right _ hpairs

private lemma satisfiesOverlapCond_zero_rows (ζ b : ℕ) (ω : SketchSample ζ b 0) (η : ℝ) :
    SatisfiesOverlapCond (sparseStackOmega ω) η := by
  have hemp : overlapPairs (sparseStackOmega ω) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro uv _
    exact Fin.elim0 uv.1
  simp [SatisfiesOverlapCond, overlapPairCount, hemp]

private lemma uniformProb_satisfiesOverlapCond_ge
    (n ζ b : ℕ) (hζ : 1 ≤ ζ) (hb : 1 ≤ b) :
    (9 / 10 : ℝ) ≤ uniformProb (SketchSample ζ b n)
      (fun ω => SatisfiesOverlapCond (sparseStackOmega ω)
        (5 * (ζ : ℝ) ^ 4 / (2 * ((ζ * b : ℕ) : ℝ)))) := by
  set η : ℝ := 5 * (ζ : ℝ) ^ 4 / (2 * ((ζ * b : ℕ) : ℝ))
  have hb0 : 0 < b := by omega
  rw [show uniformProb (SketchSample ζ b n) =
      SparseStack.uniformProb (SparseStack.SketchSample ζ b n) from rfl,
    SparseStack.uniformProb_eq_prob hb0]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have huniv : {ω : SketchSample ζ b 0 |
        SatisfiesOverlapCond (sparseStackOmega ω) η} = Set.univ := by
      ext ω
      simp [satisfiesOverlapCond_zero_rows]
    rw [huniv, (SparseStack.sketchLaw ζ b 0 hb0).prob_univ]
    norm_num
  · let μ := SparseStack.sketchLaw ζ b n hb0
    change (9 / 10 : ℝ) ≤ μ.prob {ω | SatisfiesOverlapCond (sparseStackOmega ω) η}
    set T : ℝ := η * ((n : ℝ) ^ 2 / ((ζ * b : ℕ) : ℝ))
    have hζ0 : (0 : ℝ) < (ζ : ℝ) := Nat.cast_pos.2 (by omega)
    have hb0' : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.2 hb0
    have hn0' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn0
    have hT_pos : 0 < T := by
      simp only [T, η, Nat.cast_mul]
      exact mul_pos (div_pos (mul_pos (by norm_num) (pow_pos hζ0 4))
        (mul_pos (by norm_num) (mul_pos hζ0 hb0')))
        (div_pos (pow_pos hn0' 2) (mul_pos hζ0 hb0'))
    have hT_tenth : (1 / 10 : ℝ) * T =
        (ζ : ℝ) ^ 2 * (n : ℝ) ^ 2 / (4 * (b : ℝ) ^ 2) := by
      have hden1 : (10 : ℝ) * ((2 * ((ζ : ℝ) * (b : ℝ))) * ((ζ : ℝ) * (b : ℝ))) ≠ 0 :=
        ne_of_gt (mul_pos (by norm_num) (mul_pos (mul_pos (by norm_num) (mul_pos hζ0 hb0'))
          (mul_pos hζ0 hb0')))
      have hden2 : (4 : ℝ) * (b : ℝ) ^ 2 ≠ 0 :=
        ne_of_gt (mul_pos (by norm_num) (pow_pos hb0' 2))
      simp only [T, η, Nat.cast_mul, div_mul_div_comm]
      rw [div_eq_div_iff hden1 hden2]
      ring
    have hcard_ne : (Fintype.card (SketchSample ζ b n) : ℝ) ≠ 0 :=
      SparseStack.card_sketchSample_ne_zero (s := ζ) (n := n) hb0
    have hcard_pos : (0 : ℝ) < (Fintype.card (SketchSample ζ b n) : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) hcard_ne.symm
    have hsum_real :
        (4 : ℝ) * (b : ℝ) ^ 2 *
            (∑ ω : SketchSample ζ b n, (overlapPairCount (sparseStackOmega ω) : ℝ)) ≤
          (ζ : ℝ) ^ 2 * (n : ℝ) ^ 2 * (Fintype.card (SketchSample ζ b n) : ℝ) := by
      have hcast : ((4 * b ^ 2 *
          ∑ ω : SketchSample ζ b n, overlapPairCount (sparseStackOmega ω) : ℕ) : ℝ) ≤
          ((ζ ^ 2 * n ^ 2 * Fintype.card (SketchSample ζ b n) : ℕ) : ℝ) :=
        Nat.cast_le.2 (four_mul_sq_mul_sum_overlapPairCount_le n ζ b)
      push_cast at hcast
      exact hcast
    have hexp_le :
        μ.expect (fun ω => (overlapPairCount (sparseStackOmega ω) : ℝ)) ≤
          (1 / 10 : ℝ) * T := by
      rw [SparseStack.sketchLaw_expect_eq_sum hb0, hT_tenth,
        div_le_div_iff₀ hcard_pos (mul_pos (by norm_num) (pow_pos hb0' 2))]
      calc (∑ ω : SketchSample ζ b n, (overlapPairCount (sparseStackOmega ω) : ℝ)) *
              (4 * (b : ℝ) ^ 2)
          = (4 : ℝ) * (b : ℝ) ^ 2 *
              ∑ ω : SketchSample ζ b n, (overlapPairCount (sparseStackOmega ω) : ℝ) := by ring
        _ ≤ (ζ : ℝ) ^ 2 * (n : ℝ) ^ 2 * (Fintype.card (SketchSample ζ b n) : ℝ) := hsum_real
    let S : Set (SketchSample ζ b n) := {ω | SatisfiesOverlapCond (sparseStackOmega ω) η}
    have hsub : Sᶜ ⊆ {ω : SketchSample ζ b n |
        T ≤ (overlapPairCount (sparseStackOmega ω) : ℝ)} := by
      intro ω hω
      have hnot : ¬ ((overlapPairCount (sparseStackOmega ω) : ℝ) ≤ T) := hω
      exact le_of_lt (lt_of_not_ge hnot)
    have hcompl_le : μ.prob Sᶜ ≤ 1 / 10 := by
      calc μ.prob Sᶜ
          ≤ μ.prob {ω : SketchSample ζ b n |
              T ≤ (overlapPairCount (sparseStackOmega ω) : ℝ)} := μ.prob_mono hsub
        _ ≤ μ.expect (fun ω => (overlapPairCount (sparseStackOmega ω) : ℝ)) / T :=
            μ.markov (fun _ => Nat.cast_nonneg _) hT_pos
        _ ≤ ((1 / 10 : ℝ) * T) / T :=
            div_le_div_of_nonneg_right hexp_le (le_of_lt hT_pos)
        _ = 1 / 10 := mul_div_cancel_right₀ (1 / 10 : ℝ) (ne_of_gt hT_pos)
    have hprob_compl := μ.prob_compl S
    change (9 / 10 : ℝ) ≤ μ.prob S
    linarith

/-- **Proposition (SparseStack satisfies Definition 1.2, pp. 3–4).** -/
theorem proposition_SparseStack_Overlap : Proposition_SparseStack_Overlap := by
  intro n ζ b hζ hb
  have hprob := uniformProb_satisfiesOverlapCond_ge n ζ b hζ hb
  refine ⟨?_, hprob⟩
  unfold SatisfiesOverlapWhp
  rw [Osi.Prelim.sparseStackMeasure_toReal_eq_uniformProb ζ b n hb]
  exact hprob

end Osi.UpperBound

