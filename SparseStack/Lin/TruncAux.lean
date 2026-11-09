import Mathlib
import SparseStack.Basic.Defs
import SparseFockFormal.FiniteProbability

/-!
# Helpers for `lem:gaussian-truncation` (paper, lines 434–470)

* `sum_min_sub_le_distSparseSq`: the pointwise bound (eq. pointwise-truncation, line 446)
  `d_m(z)² ≥ ∑_i min{z_i², T} - m T`;
* `sub_sq_div_le_min`: `min{y, 3t} ≥ y - y²/(12t)` (the inequality `(x - A)_+ ≤ x²/(4A)` with
  `A = 3t`, line 452);
* `coord_trunc_bound`: for a real random variable `G` with `E G⁴ ≤ 3 (E G²)²` and `t ≥ 0`,
  `E min{G², 3t} ≥ (3/4) min{E G², t}`. For `E G² ≤ t` this is the paper's bound for `i > j`;
  for `E G² > t` the paper's Gaussian scaling is replaced by the pointwise scaling
  `G ↦ √(t / E G²) G`, which can only decrease `min{G², 3t}` (lines 460–467);
* `tail_select`: with `t = a_(k+1)` (the largest entry outside a top-`k` set), the tail sum is
  at most `∑_i min{a_i, t} - k t` (the bookkeeping `(3/4) j - 3 m = 0` of line 468).
* basic facts on `distSparseSq` and `sqNorm` used by the certificate.
-/

namespace SparseStack.Lin

open SparseFock

/-! ## `sqNorm` and `distSparseSq` -/

lemma sqNorm_nonneg_aux {ι : Type} [Fintype ι] (v : ι → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma sqNorm_smul_aux {ι : Type} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    sqNorm (c • v) = c ^ 2 * sqNorm v := by
  unfold sqNorm
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- An isometry (`QᵀQ = 1`) preserves `sqNorm`. -/
lemma sqNorm_mulVec_of_isometry {k l : Type} [Fintype k] [Fintype l] [DecidableEq l]
    (Q : Matrix k l ℝ) (hQ : Q.transpose * Q = 1) (x : l → ℝ) :
    sqNorm (Q.mulVec x) = sqNorm x := by
  unfold sqNorm
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
    Matrix.one_mulVec]

lemma nonempty_cardLe (n k : ℕ) : Nonempty {S : Finset (Fin n) // S.card ≤ k} :=
  ⟨⟨∅, by simp⟩⟩

lemma distSparseSq_nonneg_aux (m : ℕ) {n : ℕ} (z : Fin n → ℝ) : 0 ≤ distSparseSq m z := by
  have := nonempty_cardLe n m
  unfold distSparseSq
  exact le_ciInf (fun I => Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))

lemma distSparseSq_le_sqNorm_aux (m : ℕ) {n : ℕ} (z : Fin n → ℝ) :
    distSparseSq m z ≤ sqNorm z := by
  unfold distSparseSq
  refine (ciInf_le (Set.finite_range _).bddBelow ⟨∅, by simp⟩).trans ?_
  simp [sqNorm, dotProduct, sq]

lemma distSparseSq_smul_aux (m : ℕ) {n : ℕ} (c : ℝ) (z : Fin n → ℝ) :
    distSparseSq m (c • z) = c ^ 2 * distSparseSq m z := by
  unfold distSparseSq
  rw [Real.mul_iInf_of_nonneg (sq_nonneg c)]
  congr 1
  funext I
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## The pointwise truncation bound -/

/-- Eq. (pointwise-truncation): `d_m(z)² ≥ ∑_i min{z_i², T} - m T` for `T ≥ 0`. -/
lemma sum_min_sub_le_distSparseSq (m : ℕ) {n : ℕ} (z : Fin n → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∑ i, min (z i ^ 2) T - m * T ≤ distSparseSq m z := by
  have := nonempty_cardLe n m
  unfold distSparseSq
  refine le_ciInf (fun I => ?_)
  obtain ⟨I, hI⟩ := I
  show ∑ i, min (z i ^ 2) T - m * T ≤ ∑ i ∈ Iᶜ, z i ^ 2
  rw [← Finset.sum_add_sum_compl I (fun i => min (z i ^ 2) T)]
  have h1 : ∑ i ∈ I, min (z i ^ 2) T ≤ m * T := by
    calc ∑ i ∈ I, min (z i ^ 2) T ≤ ∑ _i ∈ I, T :=
          Finset.sum_le_sum (fun i _ => min_le_right _ _)
      _ = (I.card : ℝ) * T := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ m * T := mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hT
  have h2 : ∑ i ∈ Iᶜ, min (z i ^ 2) T ≤ ∑ i ∈ Iᶜ, z i ^ 2 :=
    Finset.sum_le_sum (fun i _ => min_le_left _ _)
  linarith

/-! ## One coordinate -/

/-- `min{y, 3t} ≥ y - y²/(12t)` for every real `y` and `t > 0`. -/
lemma sub_sq_div_le_min (y : ℝ) {t : ℝ} (ht : 0 < t) : y - y ^ 2 / (12 * t) ≤ min y (3 * t) := by
  have h12 : 0 < 12 * t := by positivity
  refine le_min ?_ ?_
  · have : 0 ≤ y ^ 2 / (12 * t) := by positivity
    linarith
  · have key : y - y ^ 2 / (12 * t) - 3 * t = -((y - 6 * t) ^ 2) / (12 * t) := by
      field_simp
      ring
    have hneg : -((y - 6 * t) ^ 2) / (12 * t) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) h12.le
    linarith

/-- One coordinate of `lem:gaussian-truncation`: if `E G⁴ ≤ 3 (E G²)²` and `t ≥ 0`, then
`E min{G², 3t} ≥ (3/4) min{E G², t}`. -/
lemma coord_trunc_bound {Ω : Type} [Fintype Ω] (μ : FiniteLaw Ω) (G : Ω → ℝ)
    (h4 : μ.expect (fun ω => G ω ^ 4) ≤ 3 * (μ.expect (fun ω => G ω ^ 2)) ^ 2)
    {t : ℝ} (ht : 0 ≤ t) :
    3 / 4 * min (μ.expect (fun ω => G ω ^ 2)) t ≤
      μ.expect (fun ω => min (G ω ^ 2) (3 * t)) := by
  obtain ⟨A, hA⟩ : ∃ A, μ.expect (fun ω => G ω ^ 2) = A := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := hA ▸ μ.expect_nonneg (fun ω => sq_nonneg (G ω))
  rw [hA] at h4 ⊢
  rcases ht.eq_or_lt with rfl | htpos
  · have hz : ∀ ω, min (G ω ^ 2) (3 * 0) = 0 := fun ω => by
      rw [mul_zero]
      exact min_eq_right (sq_nonneg _)
    rw [FiniteLaw.expect_congr _ hz, FiniteLaw.expect_zero, min_eq_right hA0]
    norm_num
  · -- for every `c ∈ [0,1]`: `E min{G², 3t} ≥ c A - c² A²/(4t)`
    have hgen : ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
        c * A - c ^ 2 * A ^ 2 / (4 * t) ≤ μ.expect (fun ω => min (G ω ^ 2) (3 * t)) := by
      intro c hc0 hc1
      have hpt : ∀ ω, c * G ω ^ 2 - c ^ 2 / (12 * t) * G ω ^ 4 ≤ min (G ω ^ 2) (3 * t) := by
        intro ω
        have h1 := sub_sq_div_le_min (c * G ω ^ 2) htpos
        have h2 : min (c * G ω ^ 2) (3 * t) ≤ min (G ω ^ 2) (3 * t) :=
          min_le_min (mul_le_of_le_one_left (sq_nonneg _) hc1) le_rfl
        have h3 : c * G ω ^ 2 - (c * G ω ^ 2) ^ 2 / (12 * t) =
            c * G ω ^ 2 - c ^ 2 / (12 * t) * G ω ^ 4 := by
          ring
        linarith
      have hE := μ.expect_mono hpt
      rw [FiniteLaw.expect_sub, FiniteLaw.expect_smul, FiniteLaw.expect_smul, hA] at hE
      have hc2 : 0 ≤ c ^ 2 / (12 * t) := by positivity
      have h5 : c ^ 2 / (12 * t) * μ.expect (fun ω => G ω ^ 4) ≤ c ^ 2 / (12 * t) * (3 * A ^ 2) :=
        mul_le_mul_of_nonneg_left h4 hc2
      have h6 : c ^ 2 / (12 * t) * (3 * A ^ 2) = c ^ 2 * A ^ 2 / (4 * t) := by
        field_simp
        ring
      linarith
    rcases le_or_gt A t with hAt | hAt
    · have h1 := hgen 1 zero_le_one le_rfl
      simp only [one_pow, one_mul] at h1
      rw [min_eq_left hAt]
      have hAA : A ^ 2 / (4 * t) ≤ A / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    · have hApos : 0 < A := lt_of_le_of_lt ht hAt
      have h1 := hgen (t / A) (by positivity) (by rw [div_le_one hApos]; exact hAt.le)
      rw [min_eq_right hAt.le]
      have h7 : t / A * A - (t / A) ^ 2 * A ^ 2 / (4 * t) = 3 / 4 * t := by
        field_simp
        ring
      linarith

/-! ## Choosing the threshold -/

/-- With `t` the largest entry outside a top-`k` set (or `t = 0` if `n ≤ k`):
`min_{|S| ≤ k} ∑_{i ∉ S} a_i ≤ ∑_i min{a_i, t} - k t`. -/
lemma tail_select {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (k : ℕ) :
    ∃ t : ℝ, 0 ≤ t ∧
      (⨅ S : {S : Finset (Fin n) // S.card ≤ k}, ∑ i ∈ (S.1)ᶜ, a i) ≤
        ∑ i, min (a i) t - k * t := by
  classical
  rcases le_or_gt n k with hnk | hkn
  · refine ⟨0, le_rfl, ?_⟩
    refine (ciInf_le (Set.finite_range _).bddBelow
      ⟨Finset.univ, by simpa using hnk⟩).trans ?_
    have hmin : ∀ i, min (a i) 0 = 0 := fun i => min_eq_right (ha i)
    simp [hmin]
  · have hne : (Finset.powersetCard k (Finset.univ : Finset (Fin n))).Nonempty := by
      rw [Finset.powersetCard_nonempty, Finset.card_univ, Fintype.card_fin]
      exact hkn.le
    obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image _ (fun S => ∑ i ∈ S, a i) hne
    have hScard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    have hSc : (Sᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨j0, hj0, hj0t⟩ := Finset.exists_mem_eq_sup' hSc a
    have hj0S : j0 ∉ S := Finset.mem_compl.mp hj0
    have hle_out : ∀ j ∈ Sᶜ, a j ≤ a j0 := fun j hj => (Finset.le_sup' a hj).trans_eq hj0t
    have hge_in : ∀ i ∈ S, a j0 ≤ a i := by
      intro i hi
      by_contra hlt
      push Not at hlt
      have hnot : j0 ∉ S.erase i := fun h => hj0S (Finset.mem_of_mem_erase h)
      have hS'mem : insert j0 (S.erase i) ∈ Finset.powersetCard k Finset.univ := by
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.subset_univ _, ?_⟩
        rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hi, hScard]
        have : 1 ≤ k := hScard ▸ Finset.card_pos.mpr ⟨i, hi⟩
        omega
      have hsum : ∑ x ∈ insert j0 (S.erase i), a x = a j0 + (∑ x ∈ S, a x - a i) := by
        rw [Finset.sum_insert hnot, ← Finset.add_sum_erase S a hi]
        ring
      have hcmp := hmax _ hS'mem
      rw [hsum] at hcmp
      linarith
    refine ⟨a j0, ha j0, ?_⟩
    refine (ciInf_le (Set.finite_range _).bddBelow ⟨S, hScard.le⟩).trans ?_
    show ∑ i ∈ Sᶜ, a i ≤ ∑ i, min (a i) (a j0) - k * a j0
    rw [← Finset.sum_add_sum_compl S (fun i => min (a i) (a j0))]
    have h1 : ∑ i ∈ S, min (a i) (a j0) = k * a j0 := by
      rw [Finset.sum_congr rfl (fun i hi => min_eq_right (hge_in i hi)), Finset.sum_const, hScard,
        nsmul_eq_mul]
    have h2 : ∑ i ∈ Sᶜ, min (a i) (a j0) = ∑ i ∈ Sᶜ, a i :=
      Finset.sum_congr rfl (fun i hi => min_eq_left (hle_out i hi))
    rw [h1, h2]
    linarith

end SparseStack.Lin
