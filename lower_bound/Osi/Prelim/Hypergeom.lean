import Osi.Spec

/-!
# Preliminaries: Uniform Subset Sampling and Hypergeometric Bounds

Blueprint contracts for uniform `r`-subset probabilities (`uniformSubsetProb`), sequential exposure
without replacement, two-stage subsampling equivalence (`V₀ ∈ ([n] choose n₀)` then
`R ∈ (V₀ choose r)`), single-set inclusion bounds, and 1D Chebyshev hypergeometric negative
correlation for disjoint vertex sets.
-/

namespace Osi.Prelim

open Osi.Spec

/-! ## Internal combinatorial and moment helpers -/

private lemma toFinset_card_eq_filter {n r : ℕ} (E : Finset (Fin n) → Prop) [DecidablePred E] :
    (Set.toFinite {R : Finset (Fin n) | R.card = r ∧ E R}).toFinset =
      ((Finset.univ : Finset (Fin n)).powersetCard r).filter E := by
  ext R
  simp [Finset.mem_powersetCard]

private lemma toFinset_subset_card_eq_filter {n r : ℕ} (V₀ : Finset (Fin n))
    (E : Finset (Fin n) → Prop) [DecidablePred E] :
    (Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ E R}).toFinset =
      (V₀.powersetCard r).filter E := by
  ext R
  simp [Finset.mem_powersetCard, and_assoc]

private lemma uniformSubsetProb_eq_filter (n r : ℕ) (E : Finset (Fin n) → Prop)
    [DecidablePred E] :
    uniformSubsetProb n r E =
      ((((Finset.univ : Finset (Fin n)).powersetCard r).filter E).card : ℝ) /
        (Nat.choose n r : ℝ) := by
  unfold uniformSubsetProb
  rw [toFinset_card_eq_filter]

private lemma card_powersetCard_univ (n r : ℕ) :
    ((Finset.univ : Finset (Fin n)).powersetCard r).card = Nat.choose n r := by
  simp [Finset.card_powersetCard]

private lemma sq_sum_boole {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (∑ x ∈ s, (if P x then (1 : ℝ) else 0)) ^ 2 =
      ∑ x ∈ s, ∑ y ∈ s, (if P x ∧ P y then (1 : ℝ) else 0) := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hx : P x <;> by_cases hy : P y <;> simp [hx, hy]

private lemma sum_sum_boole_comm {α β : Type*} (Ω : Finset β) (S : Finset α)
    (P : α → β → Prop) [∀ a b, Decidable (P a b)] :
    ∑ ω ∈ Ω, ∑ a ∈ S, (if P a ω then (1 : ℝ) else 0) =
      ∑ a ∈ S, ((Ω.filter (fun ω => P a ω)).card : ℝ) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp

private lemma sum_sq_sum_boole {α β : Type*} (Ω : Finset β) (S : Finset α)
    (P : α → β → Prop) [∀ a b, Decidable (P a b)] :
    ∑ ω ∈ Ω, (∑ a ∈ S, (if P a ω then (1 : ℝ) else 0)) ^ 2 =
      ∑ a₁ ∈ S, ∑ a₂ ∈ S, ((Ω.filter (fun ω => P a₁ ω ∧ P a₂ ω)).card : ℝ) := by
  have hsq : ∀ ω : β,
      (∑ a ∈ S, (if P a ω then (1 : ℝ) else 0)) ^ 2 =
        ∑ a₁ ∈ S, ∑ a₂ ∈ S, (if P a₁ ω ∧ P a₂ ω then (1 : ℝ) else 0) :=
    fun ω => sq_sum_boole S (fun a => P a ω)
  simp_rw [hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  simp

private lemma double_sum_ite_add {α : Type*} [DecidableEq α] (s : Finset α) (A K : ℝ) :
    ∑ x ∈ s, ∑ y ∈ s, ((if x = y then A else 0) + K) =
      (s.card : ℝ) * A + (s.card : ℝ) ^ 2 * K := by
  have hinner : ∀ x ∈ s, ∑ y ∈ s, ((if x = y then A else 0) + K) = A + (s.card : ℝ) * K := by
    intro x hx
    rw [Finset.sum_add_distrib]
    simp [hx]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  ring

private lemma sum_sub_sq_eq {α : Type*} (s : Finset α) (f : α → ℝ) (m : ℝ)
    (hsum : ∑ x ∈ s, f x = (s.card : ℝ) * m) :
    ∑ x ∈ s, (f x - m) ^ 2 = (∑ x ∈ s, f x ^ 2) - (s.card : ℝ) * m ^ 2 := by
  have h1 : ∀ x : α, (f x - m) ^ 2 = f x ^ 2 - 2 * m * f x + m ^ 2 := fun _ => by ring
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
    nsmul_eq_mul]
  ring

private lemma sub_mul_le_mul_sub {r m n : ℕ} (hrm : r ≤ m) (hmn : m ≤ n) :
    (m - r) * n ≤ m * (n - r) := by
  have hrn : r ≤ n := hrm.trans hmn
  have h1 : (m - r) * n + r * m ≤ (m - r) * n + r * n :=
    Nat.add_le_add_left (Nat.mul_le_mul_left r hmn) _
  have h2 : (m - r) * n + r * n = m * n := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hrm]
  have h3 : m * (n - r) + r * m = m * n := by
    rw [Nat.mul_comm r m, ← Nat.mul_add, Nat.sub_add_cancel hrn]
  omega

private lemma choose_mul_pow_le {m n : ℕ} (hmn : m ≤ n) :
    ∀ r : ℕ, m.choose r * n ^ r ≤ n.choose r * m ^ r
  | 0 => by simp
  | r + 1 => by
    by_cases hmr : r + 1 ≤ m
    · refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos r)
      have hm_step : m.choose (r + 1) * (r + 1) = m.choose r * (m - r) :=
        Nat.choose_succ_right_eq m r
      have hn_step : n.choose (r + 1) * (r + 1) = n.choose r * (n - r) :=
        Nat.choose_succ_right_eq n r
      calc
        m.choose (r + 1) * n ^ (r + 1) * (r + 1)
            = (m.choose (r + 1) * (r + 1)) * n ^ (r + 1) := by ring
        _ = (m.choose r * n ^ r) * ((m - r) * n) := by rw [hm_step, pow_succ]; ring
        _ ≤ (n.choose r * m ^ r) * (m * (n - r)) :=
            Nat.mul_le_mul (choose_mul_pow_le hmn r) (sub_mul_le_mul_sub (by omega) hmn)
        _ = (n.choose (r + 1) * (r + 1)) * m ^ (r + 1) := by rw [hn_step, pow_succ]; ring
        _ = n.choose (r + 1) * m ^ (r + 1) * (r + 1) := by ring
    · have h0 : m.choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h0]

private lemma mul_choose_sub_one {n n₀ : ℕ} (hn₀ : 1 ≤ n₀) (hle : n₀ ≤ n) :
    n * (n - 1).choose (n₀ - 1) = n.choose n₀ * n₀ := by
  have hn1 : n - 1 + 1 = n := by omega
  have hn₀1 : n₀ - 1 + 1 = n₀ := by omega
  simpa [hn1, hn₀1] using Nat.add_one_mul_choose_eq (n - 1) (n₀ - 1)

private lemma mul_choose_sub_two {n n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hle : n₀ ≤ n) :
    n * (n - 1) * (n - 2).choose (n₀ - 2) = n.choose n₀ * (n₀ * (n₀ - 1)) := by
  have h1 : (n - 1) * (n - 2).choose (n₀ - 2) = (n - 1).choose (n₀ - 1) * (n₀ - 1) := by
    have hn2 : n - 2 + 1 = n - 1 := by omega
    have hn₀2 : n₀ - 2 + 1 = n₀ - 1 := by omega
    simpa [hn2, hn₀2] using Nat.add_one_mul_choose_eq (n - 2) (n₀ - 2)
  have h2 : n * (n - 1).choose (n₀ - 1) = n.choose n₀ * n₀ :=
    mul_choose_sub_one (by omega) hle
  calc
    n * (n - 1) * (n - 2).choose (n₀ - 2)
        = n * ((n - 1) * (n - 2).choose (n₀ - 2)) := by ring
    _ = (n * (n - 1).choose (n₀ - 1)) * (n₀ - 1) := by rw [h1]; ring
    _ = n.choose n₀ * (n₀ * (n₀ - 1)) := by rw [h2]; ring

private lemma card_filter_mem_singleton {n n₀ : ℕ} (hn₀ : 1 ≤ n₀) (b : Fin n) :
    (((Finset.univ : Finset (Fin n)).powersetCard n₀).filter (fun V₀ => b ∈ V₀)).card =
      (n - 1).choose (n₀ - 1) := by
  have hflt :
      ((Finset.univ : Finset (Fin n)).powersetCard n₀).filter (fun V₀ => b ∈ V₀) =
        ((Finset.univ : Finset (Fin n)).powersetCard n₀).filter ({b} ⊆ ·) := by
    ext V₀
    simp
  rw [hflt, Finset.card_filter_powersetCard_subset ({b} : Finset (Fin n)) Finset.univ n₀
    (Finset.subset_univ _) (by simpa using hn₀)]
  simp

private lemma card_filter_mem_pair {n n₀ : ℕ} (hn₀ : 2 ≤ n₀) {u v : Fin n} (huv : u ≠ v) :
    (((Finset.univ : Finset (Fin n)).powersetCard n₀).filter
      (fun V₀ => u ∈ V₀ ∧ v ∈ V₀)).card = (n - 2).choose (n₀ - 2) := by
  have hflt :
      ((Finset.univ : Finset (Fin n)).powersetCard n₀).filter (fun V₀ => u ∈ V₀ ∧ v ∈ V₀) =
        ((Finset.univ : Finset (Fin n)).powersetCard n₀).filter ({u, v} ⊆ ·) := by
    ext V₀
    simp [Finset.insert_subset_iff]
  rw [hflt, Finset.card_filter_powersetCard_subset ({u, v} : Finset (Fin n)) Finset.univ n₀
    (Finset.subset_univ _) (by simp [Finset.card_pair huv, hn₀])]
  simp [Finset.card_pair huv]

private lemma card_filter_mem_pair_mul_sq_le {n n₀ : ℕ} (hn₀ : 1 ≤ n₀) (hle : n₀ ≤ n)
    {u v : Fin n} (huv : u ≠ v) :
    (((Finset.univ : Finset (Fin n)).powersetCard n₀).filter
      (fun V₀ => u ∈ V₀ ∧ v ∈ V₀)).card * n ^ 2 ≤ n.choose n₀ * n₀ ^ 2 := by
  by_cases hn₀2 : 2 ≤ n₀
  · rw [card_filter_mem_pair hn₀2 huv]
    have hpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    have hid := mul_choose_sub_two hn₀2 hle
    have hsub : (n₀ - 1) * n ≤ n₀ * (n - 1) := sub_mul_le_mul_sub hn₀ hle
    calc
      (n - 2).choose (n₀ - 2) * n ^ 2 * (n * (n - 1))
          = (n * (n - 1) * (n - 2).choose (n₀ - 2)) * n ^ 2 := by ring
      _ = n.choose n₀ * n₀ * n * ((n₀ - 1) * n) := by rw [hid]; ring
      _ ≤ n.choose n₀ * n₀ * n * (n₀ * (n - 1)) := Nat.mul_le_mul_left _ hsub
      _ = n.choose n₀ * n₀ ^ 2 * (n * (n - 1)) := by ring
  · have hn₀_eq : n₀ = 1 := by omega
    have hempty :
        (((Finset.univ : Finset (Fin n)).powersetCard n₀).filter
          (fun V₀ => u ∈ V₀ ∧ v ∈ V₀)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro V₀ hV₀ ⟨hu, hv⟩
      rw [Finset.mem_powersetCard] at hV₀
      have hpair : ({u, v} : Finset (Fin n)) ⊆ V₀ := by
        simp [Finset.insert_subset_iff, hu, hv]
      have hcard_le : ({u, v} : Finset (Fin n)).card ≤ V₀.card := Finset.card_le_card hpair
      rw [Finset.card_pair huv, hV₀.2, hn₀_eq] at hcard_le
      omega
    simp [hempty]

private lemma choose_mul_pow_le_sub {n₀ r B : ℕ} (hr : r ≤ n₀) (hB2 : 2 * B ≤ r) :
    ∀ k : ℕ, k ≤ B → n₀.choose r * r ^ k ≤ (n₀ - k).choose (r - k) * (2 * n₀) ^ k
  | 0, _ => by simp
  | k + 1, hk1 => by
    have ih := choose_mul_pow_le_sub hr hB2 k (by omega)
    have hstep_eq :
        (n₀ - k) * (n₀ - (k + 1)).choose (r - (k + 1)) =
          (n₀ - k).choose (r - k) * (r - k) := by
      have hn : n₀ - (k + 1) + 1 = n₀ - k := by omega
      have hr' : r - (k + 1) + 1 = r - k := by omega
      simpa [hn, hr'] using Nat.add_one_mul_choose_eq (n₀ - (k + 1)) (r - (k + 1))
    have hr_le : r ≤ 2 * (r - k) := by omega
    have hstep :
        (n₀ - k).choose (r - k) * r ≤ (n₀ - (k + 1)).choose (r - (k + 1)) * (2 * n₀) := by
      calc
        (n₀ - k).choose (r - k) * r
            ≤ (n₀ - k).choose (r - k) * (2 * (r - k)) := Nat.mul_le_mul_left _ hr_le
        _ = 2 * ((n₀ - k).choose (r - k) * (r - k)) := by ring
        _ = 2 * ((n₀ - k) * (n₀ - (k + 1)).choose (r - (k + 1))) := by rw [← hstep_eq]
        _ ≤ 2 * (n₀ * (n₀ - (k + 1)).choose (r - (k + 1))) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ (Nat.sub_le n₀ k))
        _ = (n₀ - (k + 1)).choose (r - (k + 1)) * (2 * n₀) := by ring
    calc
      n₀.choose r * r ^ (k + 1)
          = (n₀.choose r * r ^ k) * r := by rw [pow_succ]; ring
      _ ≤ ((n₀ - k).choose (r - k) * (2 * n₀) ^ k) * r := Nat.mul_le_mul_right r ih
      _ = ((n₀ - k).choose (r - k) * r) * (2 * n₀) ^ k := by ring
      _ ≤ ((n₀ - (k + 1)).choose (r - (k + 1)) * (2 * n₀)) * (2 * n₀) ^ k :=
          Nat.mul_le_mul_right _ hstep
      _ = (n₀ - (k + 1)).choose (r - (k + 1)) * (2 * n₀) ^ (k + 1) := by rw [pow_succ]; ring

private lemma choose_sub_add_mul_le {n₀ r B : ℕ} (hr : r ≤ n₀) (hB2 : 2 * B ≤ r) :
    ∀ k : ℕ, k ≤ B →
      (n₀ - B - k).choose (r - B - k) * n₀.choose r ≤
        (n₀ - B).choose (r - B) * (n₀ - k).choose (r - k)
  | 0, _ => by simp
  | k + 1, hk1 => by
    have ih := choose_sub_add_mul_le hr hB2 k (by omega)
    have hpos : 0 < (n₀ - B - k) * (n₀ - k) := Nat.mul_pos (by omega) (by omega)
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    have heq1 :
        (n₀ - B - k) * (n₀ - B - (k + 1)).choose (r - B - (k + 1)) =
          (n₀ - B - k).choose (r - B - k) * (r - B - k) := by
      have hn1 : n₀ - B - (k + 1) + 1 = n₀ - B - k := by omega
      have hr1 : r - B - (k + 1) + 1 = r - B - k := by omega
      simpa [hn1, hr1] using Nat.add_one_mul_choose_eq (n₀ - B - (k + 1)) (r - B - (k + 1))
    have heq2 :
        (n₀ - k) * (n₀ - (k + 1)).choose (r - (k + 1)) =
          (n₀ - k).choose (r - k) * (r - k) := by
      have hn2 : n₀ - (k + 1) + 1 = n₀ - k := by omega
      have hr2 : r - (k + 1) + 1 = r - k := by omega
      simpa [hn2, hr2] using Nat.add_one_mul_choose_eq (n₀ - (k + 1)) (r - (k + 1))
    have hsub : (r - k - B) * (n₀ - k) ≤ (r - k) * (n₀ - k - B) :=
      sub_mul_le_mul_sub (by omega) (Nat.sub_le_sub_right hr k)
    have hsub' : (r - B - k) * (n₀ - k) ≤ (r - k) * (n₀ - B - k) := by
      have h1 : r - B - k = r - k - B := by omega
      have h2 : n₀ - B - k = n₀ - k - B := by omega
      simpa [h1, h2] using hsub
    calc
      (n₀ - B - (k + 1)).choose (r - B - (k + 1)) * n₀.choose r * ((n₀ - B - k) * (n₀ - k))
          = ((n₀ - B - k) * (n₀ - B - (k + 1)).choose (r - B - (k + 1))) *
              n₀.choose r * (n₀ - k) := by ring
      _ = ((n₀ - B - k).choose (r - B - k) * n₀.choose r) * ((r - B - k) * (n₀ - k)) := by
          rw [heq1]; ring
      _ ≤ ((n₀ - B).choose (r - B) * (n₀ - k).choose (r - k)) * ((r - k) * (n₀ - B - k)) :=
          Nat.mul_le_mul ih hsub'
      _ = (n₀ - B).choose (r - B) * ((n₀ - k) * (n₀ - (k + 1)).choose (r - (k + 1))) *
            (n₀ - B - k) := by rw [heq2]; ring
      _ = (n₀ - B).choose (r - B) * (n₀ - (k + 1)).choose (r - (k + 1)) *
            ((n₀ - B - k) * (n₀ - k)) := by ring

/-! ## Public blueprint contracts -/

/-- `uniformSubsetProb n r E` is non-negative. -/
theorem uniformSubsetProb_nonneg (n r : ℕ) (E : Finset (Fin n) → Prop) :
    0 ≤ uniformSubsetProb n r E := by
  unfold uniformSubsetProb
  positivity

/-- `uniformSubsetProb n r E ≤ 1`. -/
theorem uniformSubsetProb_le_one (n r : ℕ) (E : Finset (Fin n) → Prop) :
    uniformSubsetProb n r E ≤ 1 := by
  classical
  rw [uniformSubsetProb_eq_filter]
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_filter_le _ _).trans_eq (card_powersetCard_univ n r)

/-- Monotonicity of `uniformSubsetProb` on `r`-element subsets. -/
theorem uniformSubsetProb_mono {n r : ℕ} {E F : Finset (Fin n) → Prop}
    (h : ∀ R : Finset (Fin n), R.card = r → E R → F R) :
    uniformSubsetProb n r E ≤ uniformSubsetProb n r F := by
  classical
  rw [uniformSubsetProb_eq_filter, uniformSubsetProb_eq_filter]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine Nat.cast_le.mpr (Finset.card_le_card fun R hR => ?_)
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hR ⊢
  exact ⟨hR.1, h R hR.1.2 hR.2⟩

/-- Complement rule `Pr(¬ E) = 1 - Pr(E)` when `r ≤ n`. -/
theorem uniformSubsetProb_compl {n r : ℕ} (hr : r ≤ n) (E : Finset (Fin n) → Prop) :
    uniformSubsetProb n r (fun R => ¬ E R) = 1 - uniformSubsetProb n r E := by
  classical
  rw [uniformSubsetProb_eq_filter, uniformSubsetProb_eq_filter]
  have hpos : (0 : ℝ) < (Nat.choose n r : ℝ) := by exact_mod_cast Nat.choose_pos hr
  have hsum :
      ((((Finset.univ : Finset (Fin n)).powersetCard r).filter E).card : ℝ) +
        ((((Finset.univ : Finset (Fin n)).powersetCard r).filter (fun R => ¬ E R)).card : ℝ) =
        (Nat.choose n r : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not E).trans (card_powersetCard_univ n r)
  rw [eq_sub_iff_add_eq, ← add_div, add_comm, hsum, div_self hpos.ne']

/-- Union bound `Pr(E ∨ F) ≤ Pr(E) + Pr(F)` for `uniformSubsetProb`. -/
theorem uniformSubsetProb_or_le {n r : ℕ} (E F : Finset (Fin n) → Prop) :
    uniformSubsetProb n r (fun R => E R ∨ F R) ≤
      uniformSubsetProb n r E + uniformSubsetProb n r F := by
  classical
  rw [uniformSubsetProb_eq_filter, uniformSubsetProb_eq_filter, uniformSubsetProb_eq_filter,
    ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [Finset.filter_or]
  exact_mod_cast Finset.card_union_le _ _

/-- Without-replacement avoidance bound: for `r ≤ n`, `n ≥ 1`, and `A ⊆ [n]`,
`Pr_{R ∼ Unif([n] choose r)}(R ∩ A = ∅) ≤ (1 - |A| / n)^r`. -/
theorem uniformSubsetProb_disjoint_le {n r : ℕ} (hr : r ≤ n) (hn : 1 ≤ n)
    (A : Finset (Fin n)) :
    uniformSubsetProb n r (fun R => Disjoint R A) ≤
      (1 - (A.card : ℝ) / (n : ℝ)) ^ r := by
  classical
  rw [uniformSubsetProb_eq_filter]
  have hfilter :
      ((Finset.univ : Finset (Fin n)).powersetCard r).filter (fun R => Disjoint R A) =
        (Aᶜ).powersetCard r := by
    ext R
    simp [Finset.mem_powersetCard, Finset.subset_compl_iff_disjoint_right, and_comm]
  have hcard : (((Aᶜ).powersetCard r).card : ℕ) = (n - A.card).choose r := by
    simp [Finset.card_powersetCard, Finset.card_compl]
  have hAn : A.card ≤ n := by simpa using Finset.card_le_univ A
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcr_pos : (0 : ℝ) < (n.choose r : ℝ) := by exact_mod_cast Nat.choose_pos hr
  have hnat : ((n - A.card).choose r : ℝ) * (n : ℝ) ^ r ≤
      (n.choose r : ℝ) * ((n - A.card : ℕ) : ℝ) ^ r := by
    exact_mod_cast choose_mul_pow_le (Nat.sub_le n A.card) r
  have hbase : 1 - (A.card : ℝ) / (n : ℝ) = ((n - A.card : ℕ) : ℝ) / (n : ℝ) := by
    rw [Nat.cast_sub hAn, sub_div, div_self hn_pos.ne']
  rw [hfilter, hcard, hbase, div_pow, div_le_div_iff₀ hcr_pos (pow_pos hn_pos r)]
  linarith

/-- Hypergeometric upper tail via variance / Chebyshev: for `1 ≤ n₀ ≤ n` and `B ⊆ [n]`,
with `μ = n₀ · |B| / n`, for every `t > 0`,
`Pr_{V₀ ∼ Unif([n] choose n₀)}(|V₀ ∩ B| - μ ≥ t) ≤ μ / t²`. -/
theorem uniformSubsetProb_inter_card_chebyshev {n n₀ : ℕ} (hn₀ : 1 ≤ n₀) (hle : n₀ ≤ n)
    (B : Finset (Fin n)) (t : ℝ) (ht : 0 < t) :
    let μ : ℝ := (n₀ : ℝ) * (B.card : ℝ) / (n : ℝ)
    uniformSubsetProb n n₀ (fun V₀ => μ + t ≤ ((V₀ ∩ B).card : ℝ)) ≤ μ / t ^ 2 := by
  intro μ
  classical
  let Ω : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard n₀
  let X : Finset (Fin n) → ℝ := fun V₀ => ((V₀ ∩ B).card : ℝ)
  have hX_eq : ∀ V₀ : Finset (Fin n), X V₀ = ∑ b ∈ B, (if b ∈ V₀ then (1 : ℝ) else 0) := by
    intro V₀
    simp [X, Finset.inter_comm]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn₀.trans hle
  have hc_pos : (0 : ℝ) < (n.choose n₀ : ℝ) := by exact_mod_cast Nat.choose_pos hle
  have hΩ_card : (Ω.card : ℝ) = (n.choose n₀ : ℝ) := by
    exact_mod_cast card_powersetCard_univ n n₀
  have hsingle : ((n - 1).choose (n₀ - 1) : ℝ) = (n.choose n₀ : ℝ) * ((n₀ : ℝ) / (n : ℝ)) := by
    have hm : (n : ℝ) * ((n - 1).choose (n₀ - 1) : ℝ) = (n.choose n₀ : ℝ) * (n₀ : ℝ) := by
      exact_mod_cast mul_choose_sub_one hn₀ hle
    rw [← mul_div_assoc, eq_div_iff hn_pos.ne']
    linarith
  have hM1 : ∑ V₀ ∈ Ω, X V₀ = (n.choose n₀ : ℝ) * μ := by
    simp_rw [hX_eq]
    rw [sum_sum_boole_comm]
    have hconst : ∀ b ∈ B,
        ((Ω.filter (fun V₀ => b ∈ V₀)).card : ℝ) =
          (n.choose n₀ : ℝ) * ((n₀ : ℝ) / (n : ℝ)) := by
      intro b _
      rw [card_filter_mem_singleton hn₀ b, hsingle]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    dsimp [μ]
    ring
  have hM2 : ∑ V₀ ∈ Ω, X V₀ ^ 2 ≤
      (n.choose n₀ : ℝ) * μ + (n.choose n₀ : ℝ) * μ ^ 2 := by
    simp_rw [hX_eq]
    rw [sum_sq_sum_boole]
    let A : ℝ := (n.choose n₀ : ℝ) * ((n₀ : ℝ) / (n : ℝ))
    let K : ℝ := (n.choose n₀ : ℝ) * ((n₀ : ℝ) / (n : ℝ)) ^ 2
    have hterm : ∀ b₁ ∈ B, ∀ b₂ ∈ B,
        ((Ω.filter (fun V₀ => b₁ ∈ V₀ ∧ b₂ ∈ V₀)).card : ℝ) ≤
          (if b₁ = b₂ then A else 0) + K := by
      intro b₁ _ b₂ _
      by_cases hb : b₁ = b₂
      · subst hb
        have hsame : Ω.filter (fun V₀ => b₁ ∈ V₀ ∧ b₁ ∈ V₀) = Ω.filter (fun V₀ => b₁ ∈ V₀) := by
          ext V₀
          simp
        rw [hsame, card_filter_mem_singleton hn₀ b₁, hsingle, if_pos rfl]
        have hK : 0 ≤ K := by positivity
        linarith
      · rw [if_neg hb, zero_add]
        have hpair_nat :
            (((Ω.filter (fun V₀ => b₁ ∈ V₀ ∧ b₂ ∈ V₀)).card : ℝ)) * (n : ℝ) ^ 2 ≤
              (n.choose n₀ : ℝ) * (n₀ : ℝ) ^ 2 := by
          exact_mod_cast card_filter_mem_pair_mul_sq_le hn₀ hle hb
        dsimp [K]
        rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hn_pos 2)]
        exact hpair_nat
    calc
      ∑ b₁ ∈ B, ∑ b₂ ∈ B, ((Ω.filter (fun V₀ => b₁ ∈ V₀ ∧ b₂ ∈ V₀)).card : ℝ)
          ≤ ∑ b₁ ∈ B, ∑ b₂ ∈ B, ((if b₁ = b₂ then A else 0) + K) :=
            Finset.sum_le_sum fun b₁ hb₁ => Finset.sum_le_sum fun b₂ hb₂ => hterm b₁ hb₁ b₂ hb₂
      _ = (B.card : ℝ) * A + (B.card : ℝ) ^ 2 * K := double_sum_ite_add B A K
      _ = (n.choose n₀ : ℝ) * μ + (n.choose n₀ : ℝ) * μ ^ 2 := by
            dsimp [A, K, μ]
            ring
  have hvar : ∑ V₀ ∈ Ω, (X V₀ - μ) ^ 2 ≤ (n.choose n₀ : ℝ) * μ := by
    have hcent := sum_sub_sq_eq Ω X μ (by rwa [hΩ_card])
    rw [hΩ_card] at hcent
    linarith
  let Ω_bad : Finset (Finset (Fin n)) := Ω.filter (fun V₀ => μ + t ≤ X V₀)
  have hcheb : (Ω_bad.card : ℝ) * t ^ 2 ≤ (n.choose n₀ : ℝ) * μ := by
    calc
      (Ω_bad.card : ℝ) * t ^ 2
          = ∑ _V₀ ∈ Ω_bad, t ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ V₀ ∈ Ω_bad, (X V₀ - μ) ^ 2 := by
            refine Finset.sum_le_sum fun V₀ hV₀ => ?_
            have hmem : μ + t ≤ X V₀ := (Finset.mem_filter.mp hV₀).2
            exact pow_le_pow_left₀ ht.le (by linarith) 2
      _ ≤ ∑ V₀ ∈ Ω, (X V₀ - μ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
              sq_nonneg _
      _ ≤ (n.choose n₀ : ℝ) * μ := hvar
  rw [uniformSubsetProb_eq_filter]
  change (Ω_bad.card : ℝ) / (n.choose n₀ : ℝ) ≤ μ / t ^ 2
  rw [div_le_div_iff₀ hc_pos (pow_pos ht 2)]
  linarith

/-- Pair-inclusion Markov bound for colliding pairs in `V₀ ∼ Unif([n] choose n₀)`:
for any set `P` of pairs `(u, v)` with `u ≠ v`, and any `t > 0`, if `2 ≤ n₀ ≤ n` and `2 ≤ n`,
`Pr_{V₀}(#{uv ∈ P : u ∈ V₀ ∧ v ∈ V₀} ≥ t) ≤ (|P| · (n₀ (n₀ - 1)) / (n (n - 1))) / t`. -/
theorem uniformSubsetProb_pairs_markov {n n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hle : n₀ ≤ n)
    (P : Finset (Fin n × Fin n)) (hP : ∀ uv ∈ P, uv.1 ≠ uv.2) (t : ℝ) (ht : 0 < t) :
    uniformSubsetProb n n₀
        (fun V₀ => t ≤ ((P.filter (fun uv => uv.1 ∈ V₀ ∧ uv.2 ∈ V₀)).card : ℝ)) ≤
      ((P.card : ℝ) * ((n₀ : ℝ) * ((n₀ : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1))) / t := by
  classical
  let Ω : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard n₀
  let Y : Finset (Fin n) → ℝ :=
    fun V₀ => ((P.filter (fun uv => uv.1 ∈ V₀ ∧ uv.2 ∈ V₀)).card : ℝ)
  have hn2 : 2 ≤ n := hn₀.trans hle
  have hc_pos : (0 : ℝ) < (n.choose n₀ : ℝ) := by exact_mod_cast Nat.choose_pos hle
  have hn_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hn₀_cast : ((n₀ - 1 : ℕ) : ℝ) = (n₀ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n₀), Nat.cast_one]
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    rw [← hn_cast]
    exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n - 1)
  have hpair_eq :
      ((n - 2).choose (n₀ - 2) : ℝ) =
        (n.choose n₀ : ℝ) * ((n₀ : ℝ) * ((n₀ : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    have hm :
        (n : ℝ) * ((n : ℝ) - 1) * ((n - 2).choose (n₀ - 2) : ℝ) =
          (n.choose n₀ : ℝ) * ((n₀ : ℝ) * ((n₀ : ℝ) - 1)) := by
      rw [← hn_cast, ← hn₀_cast]
      exact_mod_cast mul_choose_sub_two hn₀ hle
    rw [eq_div_iff hden_pos.ne']
    linarith
  have hsumY :
      ∑ V₀ ∈ Ω, Y V₀ =
        (n.choose n₀ : ℝ) *
          ((P.card : ℝ) * ((n₀ : ℝ) * ((n₀ : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1))) := by
    have hY_eq : ∀ V₀ : Finset (Fin n),
        Y V₀ = ∑ uv ∈ P, (if uv.1 ∈ V₀ ∧ uv.2 ∈ V₀ then (1 : ℝ) else 0) := by
      intro V₀
      simp [Y]
    simp_rw [hY_eq]
    rw [sum_sum_boole_comm]
    have hconst : ∀ uv ∈ P,
        ((Ω.filter (fun V₀ => uv.1 ∈ V₀ ∧ uv.2 ∈ V₀)).card : ℝ) =
          (n.choose n₀ : ℝ) * ((n₀ : ℝ) * ((n₀ : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
      intro uv huv
      rw [card_filter_mem_pair hn₀ (hP uv huv), hpair_eq]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    ring
  let Ω_bad : Finset (Finset (Fin n)) := Ω.filter (fun V₀ => t ≤ Y V₀)
  have hmarkov :
      (Ω_bad.card : ℝ) * t ≤
        (n.choose n₀ : ℝ) *
          ((P.card : ℝ) * ((n₀ : ℝ) * ((n₀ : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1))) := by
    calc
      (Ω_bad.card : ℝ) * t
          = ∑ _V₀ ∈ Ω_bad, t := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ V₀ ∈ Ω_bad, Y V₀ := Finset.sum_le_sum fun V₀ hV₀ => (Finset.mem_filter.mp hV₀).2
      _ ≤ ∑ V₀ ∈ Ω, Y V₀ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
              Nat.cast_nonneg _
      _ = _ := hsumY
  rw [uniformSubsetProb_eq_filter]
  change (Ω_bad.card : ℝ) / (n.choose n₀ : ℝ) ≤ _
  rw [div_le_div_iff₀ hc_pos ht]
  linarith

/-- Two-stage subsampling law of total probability: for `r ≤ n₀ ≤ n`, averaging the conditional
uniform `r`-subset probability inside `V₀` over `V₀ ∼ Unif([n] choose n₀)` equals
`uniformSubsetProb n r E`. -/
theorem uniformSubsetProb_two_stage {n n₀ r : ℕ} (hr : r ≤ n₀) (hn₀ : n₀ ≤ n)
    (E : Finset (Fin n) → Prop) :
    uniformSubsetProb n r E =
      ((Nat.choose n n₀ : ℝ)⁻¹) *
        ∑ V₀ ∈ (Finset.univ : Finset (Fin n)).powersetCard n₀,
          (((Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ E R}).toFinset).card : ℝ) /
            (Nat.choose n₀ r : ℝ) := by
  classical
  rw [uniformSubsetProb_eq_filter]
  let Ω_n₀ : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard n₀
  let Ω_rE : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powersetCard r).filter E
  have hrew : ∀ V₀ : Finset (Fin n),
      (((Set.toFinite {R : Finset (Fin n) | R ⊆ V₀ ∧ R.card = r ∧ E R}).toFinset).card : ℝ) =
        ∑ R ∈ Ω_rE, (if R ⊆ V₀ then (1 : ℝ) else 0) := by
    intro V₀
    rw [toFinset_subset_card_eq_filter]
    have hflt : (V₀.powersetCard r).filter E = Ω_rE.filter (fun R => R ⊆ V₀) := by
      ext R
      simp [Ω_rE, Finset.mem_powersetCard, and_assoc, and_comm]
    rw [hflt]
    simp
  simp_rw [← Finset.sum_div, hrew]
  rw [sum_sum_boole_comm]
  have hconst : ∀ R ∈ Ω_rE,
      ((Ω_n₀.filter (fun V₀ => R ⊆ V₀)).card : ℝ) = ((n - r).choose (n₀ - r) : ℝ) := by
    intro R hR
    have hR_card : R.card = r := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hR).1).2
    have hc := Finset.card_filter_powersetCard_subset R Finset.univ n₀
      (Finset.subset_univ _) (by omega)
    simpa [Ω_n₀, hR_card] using congrArg (Nat.cast : ℕ → ℝ) hc
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hchoose :
      (n.choose n₀ : ℝ) * (n₀.choose r : ℝ) =
        (n.choose r : ℝ) * ((n - r).choose (n₀ - r) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := n) (k := n₀) (s := r) hr
  have hc_nn₀ : (n.choose n₀ : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn₀).ne'
  have hc_n₀r : (n₀.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hr).ne'
  have hc_nr : (n.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hr.trans hn₀)).ne'
  change (Ω_rE.card : ℝ) / (n.choose r : ℝ) = _
  rw [inv_mul_eq_div, div_div, div_eq_div_iff hc_nr (mul_ne_zero hc_n₀r hc_nn₀)]
  calc
    (Ω_rE.card : ℝ) * ((n₀.choose r : ℝ) * (n.choose n₀ : ℝ))
        = (Ω_rE.card : ℝ) * ((n.choose n₀ : ℝ) * (n₀.choose r : ℝ)) := by ring
    _ = (Ω_rE.card : ℝ) * ((n.choose r : ℝ) * ((n - r).choose (n₀ - r) : ℝ)) := by rw [hchoose]
    _ = (Ω_rE.card : ℝ) * ((n - r).choose (n₀ - r) : ℝ) * (n.choose r : ℝ) := by ring

/-- Disjoint-family capture failure bound via 1D Chebyshev + hypergeometric negative correlation
(Section 10, Eqs. (50)–(52), pp. 47–48): inside a fixed ground set `V₀ ⊆ [n]` of size `n₀`, let
`V_tree : Fin T → Finset (Fin n)` be `T ≥ 1` pairwise disjoint subsets of `V₀`, each of exact
size `B ≤ r / 2` (with `r ≤ n₀` and `1 ≤ B`). Let `p = C(n₀ - B, r - B) / C(n₀, r)`. Then:
1. `p ≥ (r / (2 n₀))^B`, and
2. the fraction of `r`-subsets `R ⊆ V₀` (`|R| = r`) that fail to contain EVERY `V_tree s` is at
   most `1 / (T p)` (and hence `≤ 1 / (T (r / (2 n₀))^B)`). -/
theorem disjoint_subsets_capture_chebyshev
    {n n₀ r T B : ℕ} (hV₀ : Finset (Fin n)) (hn₀ : hV₀.card = n₀)
    (hr : r ≤ n₀) (hB1 : 1 ≤ B) (hB2 : 2 * B ≤ r) (hT : 1 ≤ T)
    (V_tree : Fin T → Finset (Fin n))
    (hsub : ∀ s : Fin T, V_tree s ⊆ hV₀ ∧ (V_tree s).card = B)
    (hdisj : ∀ s u : Fin T, s ≠ u → Disjoint (V_tree s) (V_tree u)) :
    ((((Set.toFinite {R : Finset (Fin n) |
          R ⊆ hV₀ ∧ R.card = r ∧ ∀ s : Fin T, ¬ V_tree s ⊆ R}).toFinset).card : ℝ) /
        (Nat.choose n₀ r : ℝ)) ≤
      1 / ((T : ℝ) * ((r : ℝ) / (2 * (n₀ : ℝ))) ^ B) := by
  classical
  let Ω₀ : Finset (Finset (Fin n)) := hV₀.powersetCard r
  let C : ℝ := (n₀.choose r : ℝ)
  let p : ℝ := ((n₀ - B).choose (r - B) : ℝ) / C
  let N : Finset (Fin n) → ℝ :=
    fun R => ∑ s : Fin T, (if V_tree s ⊆ R then (1 : ℝ) else 0)
  have hr_pos : 0 < r := by omega
  have hn₀_pos : 0 < n₀ := lt_of_lt_of_le hr_pos hr
  have hC_pos : 0 < C := by
    dsimp [C]
    exact_mod_cast Nat.choose_pos hr
  have hp_pos : 0 < p := by
    refine div_pos ?_ hC_pos
    exact_mod_cast Nat.choose_pos (Nat.sub_le_sub_right hr B)
  have hT_pos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hΩ₀_card : (Ω₀.card : ℝ) = C := by
    simp [Ω₀, C, hn₀]
  have hcard_single : ∀ s : Fin T,
      ((Ω₀.filter (fun R => V_tree s ⊆ R)).card : ℝ) = C * p := by
    intro s
    have hc := Finset.card_filter_powersetCard_subset (V_tree s) hV₀ r (hsub s).1
      (by rw [(hsub s).2]; omega)
    rw [hn₀, (hsub s).2] at hc
    have hc_real : ((Ω₀.filter (fun R => V_tree s ⊆ R)).card : ℝ) =
        ((n₀ - B).choose (r - B) : ℝ) := by exact_mod_cast hc
    rw [hc_real]
    dsimp [p]
    rw [mul_div_cancel₀ _ hC_pos.ne']
  have hM1 : ∑ R ∈ Ω₀, N R = C * ((T : ℝ) * p) := by
    dsimp [N]
    rw [sum_sum_boole_comm]
    have hconst : ∀ s ∈ (Finset.univ : Finset (Fin T)),
        ((Ω₀.filter (fun R => V_tree s ⊆ R)).card : ℝ) = C * p := fun s _ => hcard_single s
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hM2 : ∑ R ∈ Ω₀, N R ^ 2 ≤ C * ((T : ℝ) * p) + C * ((T : ℝ) * p) ^ 2 := by
    dsimp [N]
    rw [sum_sq_sum_boole]
    have hterm : ∀ s ∈ (Finset.univ : Finset (Fin T)), ∀ u ∈ (Finset.univ : Finset (Fin T)),
        ((Ω₀.filter (fun R => V_tree s ⊆ R ∧ V_tree u ⊆ R)).card : ℝ) ≤
          (if s = u then C * p else 0) + C * p ^ 2 := by
      intro s _ u _
      by_cases hsu : s = u
      · subst hsu
        have hsame :
            Ω₀.filter (fun R => V_tree s ⊆ R ∧ V_tree s ⊆ R) =
              Ω₀.filter (fun R => V_tree s ⊆ R) := by
          ext R
          simp
        rw [hsame, hcard_single s, if_pos rfl]
        have hnonneg : 0 ≤ C * p ^ 2 := by positivity
        linarith
      · rw [if_neg hsu, zero_add]
        have hunion_flt :
            Ω₀.filter (fun R => V_tree s ⊆ R ∧ V_tree u ⊆ R) =
              Ω₀.filter (fun R => V_tree s ∪ V_tree u ⊆ R) := by
          ext R
          simp [Finset.union_subset_iff]
        have hunion_card : (V_tree s ∪ V_tree u).card = 2 * B := by
          rw [Finset.card_union_of_disjoint (hdisj s u hsu), (hsub s).2, (hsub u).2]
          ring
        have hc := Finset.card_filter_powersetCard_subset (V_tree s ∪ V_tree u) hV₀ r
          (Finset.union_subset (hsub s).1 (hsub u).1) (by rw [hunion_card]; exact hB2)
        rw [hn₀, hunion_card] at hc
        have hc_real :
            ((Ω₀.filter (fun R => V_tree s ⊆ R ∧ V_tree u ⊆ R)).card : ℝ) =
              ((n₀ - 2 * B).choose (r - 2 * B) : ℝ) := by
          rw [hunion_flt]
          exact_mod_cast hc
        have hneg_nat :
            (n₀ - 2 * B).choose (r - 2 * B) * n₀.choose r ≤
              (n₀ - B).choose (r - B) * (n₀ - B).choose (r - B) := by
          have h := choose_sub_add_mul_le hr hB2 B le_rfl
          have hnB : n₀ - B - B = n₀ - 2 * B := by omega
          have hrB : r - B - B = r - 2 * B := by omega
          simpa [hnB, hrB] using h
        have hneg_real :
            ((n₀ - 2 * B).choose (r - 2 * B) : ℝ) * C ≤
              ((n₀ - B).choose (r - B) : ℝ) ^ 2 := by
          dsimp [C]
          rw [sq]
          exact_mod_cast hneg_nat
        rw [hc_real]
        dsimp [p]
        rw [div_pow, sq C, ← mul_div_assoc, mul_comm C, mul_div_mul_right _ _ hC_pos.ne',
          le_div_iff₀ hC_pos]
        exact hneg_real
    calc
      ∑ s ∈ (Finset.univ : Finset (Fin T)), ∑ u ∈ (Finset.univ : Finset (Fin T)),
          ((Ω₀.filter (fun R => V_tree s ⊆ R ∧ V_tree u ⊆ R)).card : ℝ)
          ≤ ∑ s ∈ (Finset.univ : Finset (Fin T)), ∑ u ∈ (Finset.univ : Finset (Fin T)),
              ((if s = u then C * p else 0) + C * p ^ 2) :=
            Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun u hu => hterm s hs u hu
      _ = ((Finset.univ : Finset (Fin T)).card : ℝ) * (C * p) +
            ((Finset.univ : Finset (Fin T)).card : ℝ) ^ 2 * (C * p ^ 2) :=
            double_sum_ite_add Finset.univ (C * p) (C * p ^ 2)
      _ = C * ((T : ℝ) * p) + C * ((T : ℝ) * p) ^ 2 := by
            simp
            ring
  have hvar : ∑ R ∈ Ω₀, (N R - (T : ℝ) * p) ^ 2 ≤ C * ((T : ℝ) * p) := by
    have hcent := sum_sub_sq_eq Ω₀ N ((T : ℝ) * p) (by rwa [hΩ₀_card])
    rw [hΩ₀_card] at hcent
    linarith
  let Ω_miss : Finset (Finset (Fin n)) := Ω₀.filter (fun R => ∀ s : Fin T, ¬ V_tree s ⊆ R)
  have hcheb : (Ω_miss.card : ℝ) * ((T : ℝ) * p) ^ 2 ≤ C * ((T : ℝ) * p) := by
    calc
      (Ω_miss.card : ℝ) * ((T : ℝ) * p) ^ 2
          = ∑ _R ∈ Ω_miss, ((T : ℝ) * p) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ R ∈ Ω_miss, (N R - (T : ℝ) * p) ^ 2 := by
            refine Finset.sum_le_sum fun R hR => ?_
            have hmiss : ∀ s : Fin T, ¬ V_tree s ⊆ R := (Finset.mem_filter.mp hR).2
            have hN0 : N R = 0 := Finset.sum_eq_zero fun s _ => if_neg (hmiss s)
            rw [hN0, zero_sub, neg_sq]
      _ ≤ ∑ R ∈ Ω₀, (N R - (T : ℝ) * p) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
              sq_nonneg _
      _ ≤ C * ((T : ℝ) * p) := hvar
  have hmiss_le_inv_Tp : (Ω_miss.card : ℝ) / C ≤ 1 / ((T : ℝ) * p) := by
    have hTp_pos : 0 < (T : ℝ) * p := mul_pos hT_pos hp_pos
    rw [div_le_div_iff₀ hC_pos hTp_pos]
    nlinarith
  have hp_low : ((r : ℝ) / (2 * (n₀ : ℝ))) ^ B ≤ p := by
    have h2n₀_pos : (0 : ℝ) < 2 * (n₀ : ℝ) := by
      have : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀_pos
      linarith
    have hnat :
        C * (r : ℝ) ^ B ≤ ((n₀ - B).choose (r - B) : ℝ) * (2 * (n₀ : ℝ)) ^ B := by
      dsimp [C]
      exact_mod_cast choose_mul_pow_le_sub hr hB2 B le_rfl
    dsimp [p]
    rw [div_pow, div_le_div_iff₀ (pow_pos h2n₀_pos B) hC_pos]
    linarith
  have hq_pos : 0 < (T : ℝ) * ((r : ℝ) / (2 * (n₀ : ℝ))) ^ B := by
    have hr_real : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr_pos
    have hn₀_real : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀_pos
    positivity
  rw [toFinset_subset_card_eq_filter]
  exact hmiss_le_inv_Tp.trans
    (one_div_le_one_div_of_le hq_pos (mul_le_mul_of_nonneg_left hp_low hT_pos.le))

end Osi.Prelim
