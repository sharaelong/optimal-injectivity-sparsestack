import Osi.Spec
import Osi.Prelim.SubspaceSing
import Osi.Prelim.Hypergeom

/-!
# Section 8.1: Bipartite Row Preprocessing (`Lemma 8.1` and `Lemma 8.2`)

Proves `Lemma_8_1_HeavyRowCount` (`|I_heavy| ≤ n / 16`) and `Lemma_8_2_SmallOrOneSparseElim`
(if `|I_small| ≥ n / 16` or `|I_one| ≥ n / 16`, then `Pr_R(σ_min(S_Rᵀ)² < α) ≥ 9 / 10`).
-/

namespace Osi.LowerBound

open Osi.Spec

/-! ### Helper Lemmas for Small-Norm and One-Sparse Row Witnesses -/

private lemma mem_rowSupport_iff {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (i : Fin n) (j : Fin k) :
    j ∈ rowSupport S i ↔ S i j ≠ 0 := by
  simp [rowSupport]

private lemma disjoint_smallRows_of_minEig {n k r : ℕ}
    (S : Matrix (Fin n) (Fin k) ℝ) (R : Finset (Fin n)) (hR : R.card = r) (α : ℝ)
    (hmin : MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α) :
    Disjoint R (smallRows S α) := by
  by_contra hnd
  obtain ⟨i₀, hiR, hiS⟩ := Finset.not_disjoint_iff.mp hnd
  have hiS_lt : vecSqNorm (S i₀) < α := by simpa [smallRows] using hiS
  let y : Fin n → ℝ := fun i => if i = i₀ then 1 else 0
  have hsupp : ∀ i : Fin n, i ∉ R → y i = 0 := by
    intro i hi
    have hne : i ≠ i₀ := fun heq => hi (heq ▸ hiR)
    simp [y, hne]
  have hy_norm : vecSqNorm y = 1 := by
    unfold vecSqNorm
    rw [Finset.sum_eq_single i₀]
    · simp [y]
    · intro i _ hne
      simp [y, hne]
    · intro habs
      exact absurd (Finset.mem_univ i₀) habs
  have hmul : S.transpose.mulVec y = S i₀ := by
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [Finset.sum_eq_single i₀]
    · simp [y]
    · intro i _ hne
      simp [y, hne]
    · intro habs
      exact absurd (Finset.mem_univ i₀) habs
  have hlt : vecSqNorm (S.transpose.mulVec y) < α * vecSqNorm y := by
    rw [hmul, hy_norm, mul_one]
    exact hiS_lt
  have hy_pos : 0 < vecSqNorm y := by rw [hy_norm]; norm_num
  exact Osi.Prelim.not_minEigenvalueAtLeast_coordFrame_of_supported_witness
    S R hR α y hsupp hy_pos hlt hmin

private lemma not_minEig_of_two_oneSparse_same_col {n k r : ℕ}
    (S : Matrix (Fin n) (Fin k) ℝ) (R : Finset (Fin n)) (hR : R.card = r)
    {α : ℝ} (hα : 0 < α) (j₀ : Fin k) {i₁ i₂ : Fin n}
    (hne : i₁ ≠ i₂) (hi₁ : i₁ ∈ R) (hi₂ : i₂ ∈ R)
    (hsupp₁ : rowSupport S i₁ = {j₀}) (hsupp₂ : rowSupport S i₂ = {j₀}) :
    ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α := by
  have hS₂_ne : S i₂ j₀ ≠ 0 := by
    rw [← mem_rowSupport_iff, hsupp₂]
    exact Finset.mem_singleton_self j₀
  have hS₁_zero : ∀ j : Fin k, j ≠ j₀ → S i₁ j = 0 := by
    intro j hj
    by_contra hne0
    have hmem : j ∈ rowSupport S i₁ := (mem_rowSupport_iff S i₁ j).mpr hne0
    rw [hsupp₁, Finset.mem_singleton] at hmem
    exact hj hmem
  have hS₂_zero : ∀ j : Fin k, j ≠ j₀ → S i₂ j = 0 := by
    intro j hj
    by_contra hne0
    have hmem : j ∈ rowSupport S i₂ := (mem_rowSupport_iff S i₂ j).mpr hne0
    rw [hsupp₂, Finset.mem_singleton] at hmem
    exact hj hmem
  let y : Fin n → ℝ := fun i => if i = i₁ then S i₂ j₀ else if i = i₂ then -(S i₁ j₀) else 0
  have hsupp : ∀ i : Fin n, i ∉ R → y i = 0 := by
    intro i hi
    have hne₁ : i ≠ i₁ := fun h => hi (h ▸ hi₁)
    have hne₂ : i ≠ i₂ := fun h => hi (h ▸ hi₂)
    simp [y, hne₁, hne₂]
  have hy_pos : 0 < vecSqNorm y := by
    have hterm : 0 < (y i₁) ^ 2 := by
      simp only [y, ↓reduceIte]
      exact sq_pos_of_ne_zero hS₂_ne
    exact lt_of_lt_of_le hterm
      (Finset.single_le_sum (fun i _ => sq_nonneg (y i)) (Finset.mem_univ i₁))
  have hmul : S.transpose.mulVec y = 0 := by
    ext j
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    have hsub : ∑ i : Fin n, S i j * y i = ∑ i ∈ ({i₁, i₂} : Finset (Fin n)), S i j * y i := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro i _ hi_not
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi_not
      simp [y, hi_not.1, hi_not.2]
    rw [hsub, Finset.sum_pair hne]
    have hy₁ : y i₁ = S i₂ j₀ := by simp [y]
    have hy₂ : y i₂ = -(S i₁ j₀) := by simp [y, hne.symm]
    rw [hy₁, hy₂]
    by_cases hj : j = j₀
    · subst hj; ring
    · rw [hS₁_zero j hj, hS₂_zero j hj]; ring
  have hlt : vecSqNorm (S.transpose.mulVec y) < α * vecSqNorm y := by
    rw [hmul]
    have hz : vecSqNorm (0 : Fin k → ℝ) = 0 := by simp [vecSqNorm]
    rw [hz]
    exact mul_pos hα hy_pos
  exact Osi.Prelim.not_minEigenvalueAtLeast_coordFrame_of_supported_witness
    S R hR α y hsupp hy_pos hlt

/-! ### Branch 1: Small-Norm Rows Elimination -/

private lemma elim_of_many_smallRows {K α : ℝ} {n r k : ℕ}
    (S : Matrix (Fin n) (Fin k) ℝ)
    (hK : 1 ≤ K) (hrK : 2000000 * K ≤ (r : ℝ)) (hr : r ≤ n)
    (hsmall : (n : ℝ) / 16 ≤ ((smallRows S α).card : ℝ)) :
    (9 / 10 : ℝ) ≤ uniformSubsetProb n r
      (fun R => ∀ hR : R.card = r, ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α) := by
  have hr40_real : (40 : ℝ) ≤ (r : ℝ) := by linarith
  have hr40 : 40 ≤ r := by exact_mod_cast hr40_real
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let E : Finset (Fin n) → Prop :=
    fun R => ∀ hR : R.card = r, ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α
  have hcompl := Osi.Prelim.uniformSubsetProb_compl hr E
  have hmono : uniformSubsetProb n r (fun R => ¬ E R) ≤
      uniformSubsetProb n r (fun R => Disjoint R (smallRows S α)) := by
    refine Osi.Prelim.uniformSubsetProb_mono fun R hR hnotE => ?_
    have hmin : MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α :=
      Classical.not_not.mp fun hn => hnotE fun hR' => Subsingleton.elim hR' hR ▸ hn
    exact disjoint_smallRows_of_minEig S R hR α hmin
  have hdisj := Osi.Prelim.uniformSubsetProb_disjoint_le hr hn1 (smallRows S α)
  have hcard_le_n : ((smallRows S α).card : ℝ) ≤ (n : ℝ) := by
    have hc : (smallRows S α).card ≤ n := by
      simpa [Fintype.card_fin] using (smallRows S α).card_le_univ
    exact_mod_cast hc
  have hbase_nonneg : 0 ≤ 1 - ((smallRows S α).card : ℝ) / (n : ℝ) := by
    have hdiv_le : ((smallRows S α).card : ℝ) / (n : ℝ) ≤ 1 :=
      (div_le_one hn_pos).mpr hcard_le_n
    linarith
  have hbase_le : 1 - ((smallRows S α).card : ℝ) / (n : ℝ) ≤ 15 / 16 := by
    have hdiv_ge : (1 / 16 : ℝ) ≤ ((smallRows S α).card : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hn_pos]
      linarith
    linarith
  have hpow1 : (1 - ((smallRows S α).card : ℝ) / (n : ℝ)) ^ r ≤ (15 / 16 : ℝ) ^ r :=
    pow_le_pow_left₀ hbase_nonneg hbase_le r
  have hpow2 : (15 / 16 : ℝ) ^ r ≤ (15 / 16 : ℝ) ^ 40 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hr40
  have hnum : (15 / 16 : ℝ) ^ 40 ≤ 1 / 10 := by norm_num
  linarith

/-! ### Disjoint Column-Bucket Pair Packing Inside a Subsampled Ground Set `V₀` -/

private noncomputable def bucketPair {n : ℕ} (A : Finset (Fin n)) (m : Fin (A.card / 2)) :
    Finset (Fin n) :=
  {A.orderEmbOfFin rfl ⟨2 * m.1, by omega⟩, A.orderEmbOfFin rfl ⟨2 * m.1 + 1, by omega⟩}

private lemma bucketPair_subset {n : ℕ} (A : Finset (Fin n)) (m : Fin (A.card / 2)) :
    bucketPair A m ⊆ A := by
  intro x hx
  simp only [bucketPair, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> exact Finset.orderEmbOfFin_mem A rfl _

private lemma bucketPair_card {n : ℕ} (A : Finset (Fin n)) (m : Fin (A.card / 2)) :
    (bucketPair A m).card = 2 := by
  unfold bucketPair
  refine Finset.card_pair fun heq => ?_
  have hinj := (A.orderEmbOfFin rfl).injective heq
  have hval : 2 * m.1 = 2 * m.1 + 1 := congr_arg Fin.val hinj
  omega

private lemma bucketPair_disjoint {n : ℕ} (A : Finset (Fin n))
    {m₁ m₂ : Fin (A.card / 2)} (hne : m₁ ≠ m₂) :
    Disjoint (bucketPair A m₁) (bucketPair A m₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  have hm_ne : m₁.1 ≠ m₂.1 := Fin.val_ne_of_ne hne
  simp only [bucketPair, Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  rcases hx₁ with h₁ | h₁ <;> rcases hx₂ with h₂ | h₂
  · have h := (A.orderEmbOfFin rfl).injective (h₁.symm.trans h₂)
    simp only [Fin.mk.injEq] at h; omega
  · have h := (A.orderEmbOfFin rfl).injective (h₁.symm.trans h₂)
    simp only [Fin.mk.injEq] at h; omega
  · have h := (A.orderEmbOfFin rfl).injective (h₁.symm.trans h₂)
    simp only [Fin.mk.injEq] at h; omega
  · have h := (A.orderEmbOfFin rfl).injective (h₁.symm.trans h₂)
    simp only [Fin.mk.injEq] at h; omega

private lemma bucketPair_injective {n : ℕ} (A : Finset (Fin n)) :
    Function.Injective (bucketPair A) := by
  intro m₁ m₂ heq
  by_contra hne
  have hdisj := bucketPair_disjoint A hne
  let x : Fin n := A.orderEmbOfFin rfl ⟨2 * m₁.1, by omega⟩
  have hx₁ : x ∈ bucketPair A m₁ := by simp [bucketPair, x]
  have hx₂ : x ∈ bucketPair A m₂ := heq ▸ hx₁
  exact Finset.disjoint_left.mp hdisj hx₁ hx₂

private noncomputable def colBucket {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (V₀ : Finset (Fin n)) (j : Fin k) : Finset (Fin n) :=
  (V₀ ∩ oneSparseRows S).filter (fun i => rowSupport S i = {j})

private lemma colBucket_disjoint {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (V₀ : Finset (Fin n)) {j₁ j₂ : Fin k} (hne : j₁ ≠ j₂) :
    Disjoint (colBucket S V₀ j₁) (colBucket S V₀ j₂) := by
  rw [Finset.disjoint_left]
  intro i hi₁ hi₂
  simp only [colBucket, Finset.mem_filter] at hi₁ hi₂
  have heq : ({j₁} : Finset (Fin k)) = {j₂} := hi₁.2.symm.trans hi₂.2
  exact hne (Finset.singleton_injective heq)

private lemma sum_card_colBucket {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (V₀ : Finset (Fin n)) :
    ∑ j : Fin k, (colBucket S V₀ j).card = (V₀ ∩ oneSparseRows S).card := by
  have hbi : Finset.univ.biUnion (colBucket S V₀) = V₀ ∩ oneSparseRows S := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, colBucket, Finset.mem_filter]
    constructor
    · rintro ⟨_, hi, _⟩
      exact hi
    · intro hi
      have hone : (rowSupport S i).card = 1 := by
        have hmem := (Finset.mem_inter.mp hi).2
        simpa [oneSparseRows] using hmem
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hone
      exact ⟨j, hi, hj⟩
  rw [← hbi, Finset.card_biUnion]
  intro j₁ _ j₂ _ hne
  exact colBucket_disjoint S V₀ hne

private noncomputable def allBucketPairs {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (V₀ : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  Finset.univ.biUnion (fun j : Fin k => Finset.univ.image (bucketPair (colBucket S V₀ j)))

private lemma mem_allBucketPairs {n k : ℕ} {S : Matrix (Fin n) (Fin k) ℝ}
    {V₀ p : Finset (Fin n)} (hp : p ∈ allBucketPairs S V₀) :
    ∃ (j : Fin k) (m : Fin ((colBucket S V₀ j).card / 2)),
      p = bucketPair (colBucket S V₀ j) m := by
  simp only [allBucketPairs, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image] at hp
  obtain ⟨j, m, hm⟩ := hp
  exact ⟨j, m, hm.symm⟩

private lemma allBucketPairs_subset_and_card {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (V₀ : Finset (Fin n)) {p : Finset (Fin n)} (hp : p ∈ allBucketPairs S V₀) :
    p ⊆ V₀ ∧ p.card = 2 := by
  obtain ⟨j, m, rfl⟩ := mem_allBucketPairs hp
  refine ⟨?_, bucketPair_card _ _⟩
  intro x hx
  have hxb := bucketPair_subset (colBucket S V₀ j) m hx
  simp only [colBucket, Finset.mem_filter, Finset.mem_inter] at hxb
  exact hxb.1.1

private lemma allBucketPairs_pairwise_disjoint {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (V₀ : Finset (Fin n)) {p₁ p₂ : Finset (Fin n)}
    (hp₁ : p₁ ∈ allBucketPairs S V₀) (hp₂ : p₂ ∈ allBucketPairs S V₀) (hne : p₁ ≠ p₂) :
    Disjoint p₁ p₂ := by
  obtain ⟨j₁, m₁, rfl⟩ := mem_allBucketPairs hp₁
  obtain ⟨j₂, m₂, rfl⟩ := mem_allBucketPairs hp₂
  by_cases hj : j₁ = j₂
  · subst hj
    have hm : m₁ ≠ m₂ := fun hm_eq => hne (hm_eq ▸ rfl)
    exact bucketPair_disjoint _ hm
  · exact Disjoint.mono (bucketPair_subset _ _) (bucketPair_subset _ _)
      (colBucket_disjoint S V₀ hj)

private lemma not_minEig_of_allBucketPairs_subset {n k r : ℕ}
    (S : Matrix (Fin n) (Fin k) ℝ) (V₀ R : Finset (Fin n)) (hR : R.card = r)
    {α : ℝ} (hα : 0 < α) {p : Finset (Fin n)}
    (hp : p ∈ allBucketPairs S V₀) (hsub : p ⊆ R) :
    ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α := by
  obtain ⟨j, m, rfl⟩ := mem_allBucketPairs hp
  let i₁ : Fin n := (colBucket S V₀ j).orderEmbOfFin rfl ⟨2 * m.1, by omega⟩
  let i₂ : Fin n := (colBucket S V₀ j).orderEmbOfFin rfl ⟨2 * m.1 + 1, by omega⟩
  have hne : i₁ ≠ i₂ := by
    intro heq
    have h := ((colBucket S V₀ j).orderEmbOfFin rfl).injective heq
    simp only [Fin.mk.injEq] at h
    omega
  have hi₁_p : i₁ ∈ bucketPair (colBucket S V₀ j) m := by
    simp [bucketPair, i₁]
  have hi₂_p : i₂ ∈ bucketPair (colBucket S V₀ j) m := by
    simp [bucketPair, i₂]
  have hi₁_B : i₁ ∈ colBucket S V₀ j := bucketPair_subset (colBucket S V₀ j) m hi₁_p
  have hi₂_B : i₂ ∈ colBucket S V₀ j := bucketPair_subset (colBucket S V₀ j) m hi₂_p
  have hsupp₁ : rowSupport S i₁ = {j} := (Finset.mem_filter.mp hi₁_B).2
  have hsupp₂ : rowSupport S i₂ = {j} := (Finset.mem_filter.mp hi₂_B).2
  exact not_minEig_of_two_oneSparse_same_col S R hR hα j hne
    (hsub hi₁_p) (hsub hi₂_p) hsupp₁ hsupp₂

private lemma card_allBucketPairs_bound {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (V₀ : Finset (Fin n)) :
    (V₀ ∩ oneSparseRows S).card ≤ 2 * (allBucketPairs S V₀).card + k := by
  have hcard_eq : (allBucketPairs S V₀).card =
      ∑ j : Fin k, ((colBucket S V₀ j).card / 2) := by
    unfold allBucketPairs
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.card_image_of_injective _ (bucketPair_injective _),
        Finset.card_univ, Fintype.card_fin]
    · intro j₁ _ j₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hp₁ hp₂
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp₁ hp₂
      obtain ⟨m₁, rfl⟩ := hp₁
      obtain ⟨m₂, hm₂⟩ := hp₂
      have hdisj : Disjoint (bucketPair (colBucket S V₀ j₁) m₁)
          (bucketPair (colBucket S V₀ j₂) m₂) :=
        Disjoint.mono (bucketPair_subset _ _) (bucketPair_subset _ _)
          (colBucket_disjoint S V₀ hne)
      let x : Fin n := (colBucket S V₀ j₁).orderEmbOfFin rfl ⟨2 * m₁.1, by omega⟩
      have hx₁ : x ∈ bucketPair (colBucket S V₀ j₁) m₁ := by simp [bucketPair, x]
      have hx₂ : x ∈ bucketPair (colBucket S V₀ j₂) m₂ := hm₂ ▸ hx₁
      exact Finset.disjoint_left.mp hdisj hx₁ hx₂
  rw [← sum_card_colBucket S V₀, hcard_eq]
  have hsum_le : ∑ j : Fin k, (colBucket S V₀ j).card ≤
      ∑ j : Fin k, (2 * ((colBucket S V₀ j).card / 2) + 1) := by
    refine Finset.sum_le_sum fun j _ => ?_
    omega
  have hsum_split : ∑ j : Fin k, (2 * ((colBucket S V₀ j).card / 2) + 1) =
      2 * (∑ j : Fin k, ((colBucket S V₀ j).card / 2)) + k := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
  omega

/-! ### Conditional Capture Bound Inside a Good `V₀` and Branch 2 Assembly -/

private lemma condProb_le_of_good_V₀ {K α : ℝ} {n n₀ r k : ℕ}
    (S : Matrix (Fin n) (Fin k) ℝ) (V₀ : Finset (Fin n)) (hn₀ : V₀.card = n₀)
    (hr : r ≤ n₀) (hK : 1 ≤ K) (hα : 0 < α)
    (hrK : 2000000 * K ≤ (r : ℝ)) (hk : (k : ℝ) ≤ K * (r : ℝ))
    (hn₀_upper : (n₀ : ℝ) ≤ 64 * K * (r : ℝ))
    (hgood : 2 * K * (r : ℝ) ≤ ((V₀ ∩ oneSparseRows S).card : ℝ)) :
    (((Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧
        ¬ (∀ hR : R.card = r, ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α)}).toFinset).card : ℝ) /
      (Nat.choose n₀ r : ℝ) ≤ 1 / 20 := by
  let P := allBucketPairs S V₀
  let T := P.card
  have hpair_nat : (V₀ ∩ oneSparseRows S).card ≤ 2 * T + k :=
    card_allBucketPairs_bound S V₀
  have hpair_real : ((V₀ ∩ oneSparseRows S).card : ℝ) ≤ 2 * (T : ℝ) + (k : ℝ) := by
    exact_mod_cast hpair_nat
  have hT_lower : K * (r : ℝ) ≤ 2 * (T : ℝ) := by linarith
  have hr4_real : (4 : ℝ) ≤ (r : ℝ) := by linarith
  have hr4 : 2 * 2 ≤ r := by exact_mod_cast hr4_real
  have hKr_big : (2000000 : ℝ) ≤ K * (r : ℝ) := by nlinarith
  have hT1_real : (1 : ℝ) ≤ (T : ℝ) := by linarith
  have hT1 : 1 ≤ T := by exact_mod_cast hT1_real
  let V_tree : Fin T → Finset (Fin n) := fun idx => (P.equivFin.symm idx).1
  have hsub_tree : ∀ idx : Fin T, V_tree idx ⊆ V₀ ∧ (V_tree idx).card = 2 :=
    fun idx => allBucketPairs_subset_and_card S V₀ (P.equivFin.symm idx).2
  have hdisj_tree : ∀ s u : Fin T, s ≠ u → Disjoint (V_tree s) (V_tree u) := by
    intro s u hne
    have hval_ne : V_tree s ≠ V_tree u := fun heq =>
      hne (P.equivFin.symm.injective (Subtype.ext heq))
    exact allBucketPairs_pairwise_disjoint S V₀
      (P.equivFin.symm s).2 (P.equivFin.symm u).2 hval_ne
  have hset_le :
      (Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧
        ¬ (∀ hR : R.card = r, ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α)}).toFinset.card ≤
      (Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧
        ∀ s : Fin T, ¬ V_tree s ⊆ R}).toFinset.card := by
    refine Finset.card_le_card fun R hR_mem => ?_
    rw [Set.Finite.mem_toFinset] at hR_mem ⊢
    obtain ⟨hR_sub, hR_card, hnotE⟩ := hR_mem
    refine ⟨hR_sub, hR_card, fun s hs_sub => ?_⟩
    have hmin : MinEigenvalueAtLeast (S.transpose * coordFrame R hR_card) α :=
      Classical.not_not.mp fun hn => hnotE fun hR' => Subsingleton.elim hR' hR_card ▸ hn
    exact not_minEig_of_allBucketPairs_subset S V₀ R hR_card hα
      (P.equivFin.symm s).2 hs_sub hmin
  have hdiv_le :
      (((Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧
        ¬ (∀ hR : R.card = r, ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α)}).toFinset).card : ℝ) /
        (Nat.choose n₀ r : ℝ) ≤
      (((Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧
        ∀ s : Fin T, ¬ V_tree s ⊆ R}).toFinset).card : ℝ) / (Nat.choose n₀ r : ℝ) := by
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    exact_mod_cast hset_le
  have hcheb := Osi.Prelim.disjoint_subsets_capture_chebyshev
    V₀ hn₀ hr (by norm_num : 1 ≤ 2) hr4 hT1 V_tree hsub_tree hdisj_tree
  have hK_pos : 0 < K := by linarith
  have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hn₀_pos : (0 : ℝ) < (n₀ : ℝ) := by
    have : (0 : ℝ) < (r : ℝ) := hr_pos
    have : (r : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hr
    linarith
  have hfrac : 1 / (128 * K) ≤ (r : ℝ) / (2 * (n₀ : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsq : (1 / (128 * K)) ^ 2 ≤ ((r : ℝ) / (2 * (n₀ : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hfrac 2
  have hprod : ((1 / 2 : ℝ) * K * (r : ℝ)) * (1 / (128 * K)) ^ 2 ≤
      (T : ℝ) * ((r : ℝ) / (2 * (n₀ : ℝ))) ^ 2 := by
    refine mul_le_mul (by linarith) hsq (by positivity) (by positivity)
  have hlhs_eq : ((1 / 2 : ℝ) * K * (r : ℝ)) * (1 / (128 * K)) ^ 2 =
      (r : ℝ) / (32768 * K) := by
    field_simp
    ring
  have h20 : (20 : ℝ) ≤ (r : ℝ) / (32768 * K) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hdenom_ge : (20 : ℝ) ≤ (T : ℝ) * ((r : ℝ) / (2 * (n₀ : ℝ))) ^ 2 := by
    linarith
  have hrhs_le : 1 / ((T : ℝ) * ((r : ℝ) / (2 * (n₀ : ℝ))) ^ 2) ≤ 1 / 20 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 20) hdenom_ge
  linarith

private lemma elim_of_many_oneSparseRows {K α : ℝ} {n r k : ℕ}
    (S : Matrix (Fin n) (Fin k) ℝ)
    (hK : 1 ≤ K) (hα : 0 < α) (hrK : 2000000 * K ≤ (r : ℝ))
    (hn : 64 * K * (r : ℝ) ≤ (n : ℝ)) (hk : (k : ℝ) ≤ K * (r : ℝ)) (hr : r ≤ n)
    (hone : (n : ℝ) / 16 ≤ ((oneSparseRows S).card : ℝ)) :
    (9 / 10 : ℝ) ≤ uniformSubsetProb n r
      (fun R => ∀ hR : R.card = r, ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α) := by
  open Classical in
  let E : Finset (Fin n) → Prop :=
    fun R => ∀ hR : R.card = r, ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α
  have hcompl := Osi.Prelim.uniformSubsetProb_compl hr E
  have hr_big : (2000000 : ℝ) ≤ (r : ℝ) := by nlinarith
  have hKr_big : (2000000 : ℝ) ≤ K * (r : ℝ) := by nlinarith
  let n₀ : ℕ := ⌊64 * K * (r : ℝ)⌋₊
  have hr_le_64 : (r : ℝ) ≤ 64 * K * (r : ℝ) := by nlinarith
  have hr_n₀ : r ≤ n₀ := Nat.le_floor hr_le_64
  have hn₀_n : n₀ ≤ n := Nat.floor_le_of_le hn
  have hn₀_upper : (n₀ : ℝ) ≤ 64 * K * (r : ℝ) := Nat.floor_le (by positivity)
  have hn₀_lt_succ : 64 * K * (r : ℝ) < (n₀ : ℝ) + 1 :=
    Nat.lt_floor_add_one (64 * K * (r : ℝ))
  have hn₀_lower : 63 * K * (r : ℝ) ≤ (n₀ : ℝ) := by linarith
  have hn₀_81920 : (81920 : ℝ) ≤ (n₀ : ℝ) := by linarith
  have hn₀1 : 1 ≤ n₀ := by
    have : (1 : ℝ) ≤ (n₀ : ℝ) := by linarith
    exact_mod_cast this
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn₀_pos : (0 : ℝ) < (n₀ : ℝ) := by linarith
  let B : Finset (Fin n) := Finset.univ \ oneSparseRows S
  let μ : ℝ := (n₀ : ℝ) * (B.card : ℝ) / (n : ℝ)
  let t : ℝ := (n₀ : ℝ) / 64
  have ht : 0 < t := by positivity
  have hB_card_nat : B.card + (oneSparseRows S).card = n := by
    simpa [B, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (oneSparseRows S))
  have hB_card_real : (B.card : ℝ) + ((oneSparseRows S).card : ℝ) = (n : ℝ) := by
    exact_mod_cast hB_card_nat
  have hμ_le : μ ≤ (15 / 16 : ℝ) * (n₀ : ℝ) := by
    have hB_le : (B.card : ℝ) ≤ (15 / 16 : ℝ) * (n : ℝ) := by linarith
    unfold μ
    rw [div_le_iff₀ hn_pos]
    nlinarith
  have hcheb_bad : uniformSubsetProb n n₀ (fun V₀ => μ + t ≤ ((V₀ ∩ B).card : ℝ)) ≤ 1 / 20 := by
    have hc := Osi.Prelim.uniformSubsetProb_inter_card_chebyshev hn₀1 hn₀_n B t ht
    have hratio : μ / t ^ 2 ≤ 4096 / (n₀ : ℝ) := by
      have ht_sq : t ^ 2 = (n₀ : ℝ) ^ 2 / 4096 := by unfold t; ring
      rw [ht_sq, div_le_div_iff₀ (by positivity) hn₀_pos]
      nlinarith
    have h4096 : 4096 / (n₀ : ℝ) ≤ 1 / 20 := by
      rw [div_le_iff₀ hn₀_pos]
      linarith
    linarith
  let U₀ : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard n₀
  let condProb : Finset (Fin n) → ℝ := fun V₀ =>
    (((Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ ¬ E R}).toFinset).card : ℝ) /
      (Nat.choose n₀ r : ℝ)
  let bad : Finset (Fin n) → Prop := fun V₀ => μ + t ≤ ((V₀ ∩ B).card : ℝ)
  have hpointwise : ∀ V₀ ∈ U₀, condProb V₀ ≤ (if bad V₀ then (1 : ℝ) else 0) + 1 / 20 := by
    intro V₀ hV₀
    have hV₀_card : V₀.card = n₀ := (Finset.mem_powersetCard.mp hV₀).2
    by_cases hbad : bad V₀
    · rw [if_pos hbad]
      have hcond_le_one : condProb V₀ ≤ 1 := by
        unfold condProb
        have hchoose_pos : (0 : ℝ) < (Nat.choose n₀ r : ℝ) := by
          exact_mod_cast Nat.choose_pos hr_n₀
        rw [div_le_one hchoose_pos]
        have hc : (Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ ¬ E R}).toFinset.card ≤
            Nat.choose n₀ r := by
          rw [← hV₀_card, ← Finset.card_powersetCard]
          refine Finset.card_le_card fun R hR_mem => ?_
          rw [Set.Finite.mem_toFinset] at hR_mem
          exact Finset.mem_powersetCard.mpr ⟨hR_mem.1, hR_mem.2.1⟩
        exact_mod_cast hc
      linarith
    · rw [if_neg hbad]
      rw [zero_add]
      have hlt_bad : ((V₀ ∩ B).card : ℝ) < μ + t := not_le.mp hbad
      have hpart_nat : (V₀ ∩ oneSparseRows S).card + (V₀ ∩ B).card = n₀ := by
        have hunion : (V₀ ∩ oneSparseRows S) ∪ (V₀ ∩ B) = V₀ := by
          ext i
          simp only [B, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
            Finset.mem_univ, true_and]
          tauto
        have hdisj_part : Disjoint (V₀ ∩ oneSparseRows S) (V₀ ∩ B) := by
          rw [Finset.disjoint_left]
          intro i hi₁ hi₂
          simp only [B, Finset.mem_inter, Finset.mem_sdiff] at hi₁ hi₂
          exact hi₂.2.2 hi₁.2
        rw [← Finset.card_union_of_disjoint hdisj_part, hunion, hV₀_card]
      have hpart_real : ((V₀ ∩ oneSparseRows S).card : ℝ) + ((V₀ ∩ B).card : ℝ) = (n₀ : ℝ) := by
        exact_mod_cast hpart_nat
      have hgood : 2 * K * (r : ℝ) ≤ ((V₀ ∩ oneSparseRows S).card : ℝ) := by
        unfold t at hlt_bad
        linarith
      exact condProb_le_of_good_V₀ S V₀ hV₀_card hr_n₀ hK hα hrK hk hn₀_upper hgood
  have hsum_le : ∑ V₀ ∈ U₀, condProb V₀ ≤
      ((U₀.filter bad).card : ℝ) + (U₀.card : ℝ) * (1 / 20 : ℝ) := by
    calc
      ∑ V₀ ∈ U₀, condProb V₀
          ≤ ∑ V₀ ∈ U₀, ((if bad V₀ then (1 : ℝ) else 0) + 1 / 20) :=
        Finset.sum_le_sum hpointwise
      _ = (∑ V₀ ∈ U₀, if bad V₀ then (1 : ℝ) else 0) + ∑ _V₀ ∈ U₀, (1 / 20 : ℝ) :=
        Finset.sum_add_distrib
      _ = ((U₀.filter bad).card : ℝ) + (U₀.card : ℝ) * (1 / 20 : ℝ) := by
        rw [Finset.sum_boole, Finset.sum_const, nsmul_eq_mul]
  have hU₀_card : U₀.card = Nat.choose n n₀ := by
    simp [U₀, Finset.card_powersetCard, Fintype.card_fin]
  have hfilter_eq : U₀.filter bad =
      (Set.toFinite {V₀ : Finset (Fin n) | V₀.card = n₀ ∧ bad V₀}).toFinset := by
    ext V₀
    simp [U₀, Finset.mem_powersetCard, Finset.subset_univ]
  have hchoose_nn₀_pos : (0 : ℝ) < (Nat.choose n n₀ : ℝ) := by
    exact_mod_cast Nat.choose_pos hn₀_n
  have htwo_stage := Osi.Prelim.uniformSubsetProb_two_stage hr_n₀ hn₀_n (fun R => ¬ E R)
  have hprob_notE : uniformSubsetProb n r (fun R => ¬ E R) ≤ 1 / 10 := by
    rw [htwo_stage]
    have hmul_le : (Nat.choose n n₀ : ℝ)⁻¹ * ∑ V₀ ∈ U₀, condProb V₀ ≤
        (Nat.choose n n₀ : ℝ)⁻¹ *
          (((U₀.filter bad).card : ℝ) + (U₀.card : ℝ) * (1 / 20 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr (le_of_lt hchoose_nn₀_pos))
    have hrhs_eq : (Nat.choose n n₀ : ℝ)⁻¹ *
        (((U₀.filter bad).card : ℝ) + (U₀.card : ℝ) * (1 / 20 : ℝ)) =
        uniformSubsetProb n n₀ bad + 1 / 20 := by
      rw [hfilter_eq, hU₀_card, uniformSubsetProb]
      have hne : (Nat.choose n n₀ : ℝ) ≠ 0 := ne_of_gt hchoose_nn₀_pos
      field_simp [hne]
    linarith
  linarith

/-! ### Main Section 8.1 Theorems -/

/-- **Lemma 8.1 (Heavy-row count bound, p. 37):** `frobSq S ≤ 10 n ⇒ |heavyRows S 160| ≤ n / 16`. -/
theorem lemma_8_1_HeavyRowCount : Lemma_8_1_HeavyRowCount := by
  intro n k S hfrob
  have hle1 : (160 : ℝ) * ((heavyRows S 160).card : ℝ) ≤
      ∑ i ∈ heavyRows S 160, vecSqNorm (S i) := by
    have hcard : (160 : ℝ) * ((heavyRows S 160).card : ℝ) =
        ∑ _i ∈ heavyRows S 160, (160 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hcard]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi_lt : 160 < vecSqNorm (S i) := by simpa [heavyRows] using hi
    exact le_of_lt hi_lt
  have hle2 : ∑ i ∈ heavyRows S 160, vecSqNorm (S i) ≤ frobSq S := by
    have huniv : ∑ i : Fin n, vecSqNorm (S i) = frobSq S := rfl
    rw [← huniv]
    exact Finset.sum_le_univ_sum_of_nonneg fun i =>
      Finset.sum_nonneg fun j _ => sq_nonneg (S i j)
  linarith

/-- **Lemma 8.2 (Small-norm or one-sparse row elimination, p. 37).** -/
theorem lemma_8_2_SmallOrOneSparseElim : Lemma_8_2_SmallOrOneSparseElim := by
  refine ⟨2000000, by norm_num, ?_⟩
  intro K α n r k S hK hα hrK hn hk hr hcases
  rcases hcases with hsmall | hone
  · exact elim_of_many_smallRows S hK hrK hr hsmall
  · exact elim_of_many_oneSparseRows S hK hα hrK hn hk hr hone

end Osi.LowerBound
