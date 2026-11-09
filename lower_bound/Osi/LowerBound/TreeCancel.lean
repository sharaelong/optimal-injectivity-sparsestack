import Osi.Spec

/-!
# Sections 9.1–9.2: Single-Tree Star Cancellation and Greedy Disjoint Leaves

Proves `Lemma_9_1_TreeCancellation` and `Lemma_9_2_SingleTreeDisjointLeaves`.
-/

namespace Osi.LowerBound

open Osi.Spec

private lemma mem_rowSupport_iff {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (i : Fin n) (j : Fin k) :
    j ∈ rowSupport S i ↔ S i j ≠ 0 := by
  simp [rowSupport]

private lemma c4Free_no_two_common_cols {n k : ℕ} {S : Matrix (Fin n) (Fin k) ℝ}
    {V_G0 : Finset (Fin n)} (hC4 : IsC4FreeRows S V_G0)
    {u v : Fin n} (hu : u ∈ V_G0) (hv : v ∈ V_G0) (huv : u ≠ v)
    {c₁ c₂ : Fin k} (hc1u : c₁ ∈ rowSupport S u) (hc1v : c₁ ∈ rowSupport S v)
    (hc2u : c₂ ∈ rowSupport S u) (hc2v : c₂ ∈ rowSupport S v) :
    c₁ = c₂ :=
  Finset.card_le_one.mp (hC4 u hu v hv huv)
    c₁ (Finset.mem_inter.mpr ⟨hc1u, hc1v⟩)
    c₂ (Finset.mem_inter.mpr ⟨hc2u, hc2v⟩)

private lemma c4Free_eq_row_of_two_common_cols {n k : ℕ} {S : Matrix (Fin n) (Fin k) ℝ}
    {V_G0 : Finset (Fin n)} (hC4 : IsC4FreeRows S V_G0)
    {u v : Fin n} (hu : u ∈ V_G0) (hv : v ∈ V_G0)
    {c₁ c₂ : Fin k} (hc : c₁ ≠ c₂)
    (hc1u : c₁ ∈ rowSupport S u) (hc1v : c₁ ∈ rowSupport S v)
    (hc2u : c₂ ∈ rowSupport S u) (hc2v : c₂ ∈ rowSupport S v) :
    u = v := by
  by_contra huv
  exact hc (c4Free_no_two_common_cols hC4 hu hv huv hc1u hc1v hc2u hc2v)

private lemma mulVec_treeCancelVec_eq {n k q : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (V_G0 : Finset (Fin n)) (iStar : Fin n) (L : Fin k → Finset (Fin n))
    (hLsub : ∀ j ∈ rowSupport S iStar, L j ⊆ V_G0 \ {iStar}) (c : Fin k) :
    (S.transpose.mulVec (treeCancelVec S iStar q L)) c =
      S iStar c + ∑ j ∈ rowSupport S iStar, ∑ ℓ ∈ L j,
        S ℓ c * (-(S iStar j) / ((q : ℝ) * S ℓ j)) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ iStar)]
  have hx0 : treeCancelVec S iStar q L iStar = 1 := by simp [treeCancelVec]
  rw [hx0, mul_one]
  congr 1
  have hsum :
      ∑ m ∈ Finset.univ.erase iStar, S m c * treeCancelVec S iStar q L m =
        ∑ m ∈ Finset.univ.erase iStar, ∑ j ∈ rowSupport S iStar,
          if m ∈ L j then S m c * (-(S iStar j) / ((q : ℝ) * S m j)) else 0 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_ne : m ≠ iStar := Finset.ne_of_mem_erase hm
    simp [treeCancelVec, hm_ne, Finset.mul_sum]
  rw [hsum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_ite_mem]
  have hinter : Finset.univ.erase iStar ∩ L j = L j := by
    refine Finset.inter_eq_right.mpr fun ℓ hℓ => ?_
    have hℓ_sdiff := hLsub j hj hℓ
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hℓ_sdiff
    exact Finset.mem_erase.mpr ⟨hℓ_sdiff.2, Finset.mem_univ ℓ⟩
  rw [hinter]

private lemma sq_sum_eq_sum_sq_of_at_most_one_ne_zero {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ)
    (h : ∀ x ∈ s, ∀ y ∈ s, f x ≠ 0 → f y ≠ 0 → x = y) :
    (∑ x ∈ s, f x) ^ 2 = ∑ x ∈ s, (f x) ^ 2 := by
  by_cases hex : ∃ x ∈ s, f x ≠ 0
  · obtain ⟨x₀, hx₀, hfx₀⟩ := hex
    have hzero : ∀ y ∈ s, y ≠ x₀ → f y = 0 := by
      intro y hy hne
      by_contra hfy
      exact hne (h y hy x₀ hx₀ hfy hfx₀)
    rw [Finset.sum_eq_single x₀ hzero (fun ha => absurd hx₀ ha),
      Finset.sum_eq_single x₀ (fun y hy hne => by simp [hzero y hy hne])
        (fun ha => absurd hx₀ ha)]
  · have hex' : ∀ x ∈ s, f x = 0 := fun x hx => not_not.mp fun hfx => hex ⟨x, hx, hfx⟩
    rw [Finset.sum_eq_zero hex', Finset.sum_eq_zero (fun x hx => by simp [hex' x hx])]
    ring

private lemma vecSqNorm_pos_of_mem_rowSupport {n k : ℕ} {S : Matrix (Fin n) (Fin k) ℝ}
    {i : Fin n} {j : Fin k} (hj : j ∈ rowSupport S i) :
    0 < vecSqNorm (S i) := by
  have hne : S i j ≠ 0 := (mem_rowSupport_iff S i j).mp hj
  have hsq : 0 < (S i j) ^ 2 := sq_pos_of_ne_zero hne
  have hle : (S i j) ^ 2 ≤ vecSqNorm (S i) :=
    Finset.single_le_sum (fun c _ => sq_nonneg (S i c)) (Finset.mem_univ j)
  linarith

private lemma leaf_outer_energy_le {n k q : ℕ} {S : Matrix (Fin n) (Fin k) ℝ}
    {iStar ℓ : Fin n} {j : Fin k}
    (hq : 1 ≤ q) (hj_star : j ∈ rowSupport S iStar) (hj_ℓ : j ∈ rowSupport S ℓ)
    (hw : relWeight S iStar j ≤ relWeight S ℓ j) :
    ∑ c ∈ (rowSupport S iStar)ᶜ, (S ℓ c * (-(S iStar j) / ((q : ℝ) * S ℓ j))) ^ 2 ≤
      vecSqNorm (S iStar) / ((q : ℝ) ^ 2) := by
  have hsum_eq :
      ∑ c ∈ (rowSupport S iStar)ᶜ, (S ℓ c * (-(S iStar j) / ((q : ℝ) * S ℓ j))) ^ 2 =
        ((-(S iStar j) / ((q : ℝ) * S ℓ j)) ^ 2) * ∑ c ∈ (rowSupport S iStar)ᶜ, (S ℓ c) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hsub_norm : ∑ c ∈ (rowSupport S iStar)ᶜ, (S ℓ c) ^ 2 ≤ vecSqNorm (S ℓ) :=
    Finset.sum_le_univ_sum_of_nonneg fun c => sq_nonneg (S ℓ c)
  have hnorm_star : 0 < vecSqNorm (S iStar) := vecSqNorm_pos_of_mem_rowSupport hj_star
  have hnorm_ℓ : 0 < vecSqNorm (S ℓ) := vecSqNorm_pos_of_mem_rowSupport hj_ℓ
  have hSℓ : S ℓ j ≠ 0 := (mem_rowSupport_iff S ℓ j).mp hj_ℓ
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hq)
  have hcross : (S iStar j) ^ 2 * vecSqNorm (S ℓ) ≤ (S ℓ j) ^ 2 * vecSqNorm (S iStar) :=
    (div_le_div_iff₀ hnorm_star hnorm_ℓ).mp hw
  have hden_pos : 0 < (q : ℝ) ^ 2 * (S ℓ j) ^ 2 :=
    mul_pos (sq_pos_of_pos hq0) (sq_pos_of_ne_zero hSℓ)
  calc
    ∑ c ∈ (rowSupport S iStar)ᶜ, (S ℓ c * (-(S iStar j) / ((q : ℝ) * S ℓ j))) ^ 2
      = ((-(S iStar j) / ((q : ℝ) * S ℓ j)) ^ 2) * ∑ c ∈ (rowSupport S iStar)ᶜ, (S ℓ c) ^ 2 :=
        hsum_eq
    _ ≤ ((-(S iStar j) / ((q : ℝ) * S ℓ j)) ^ 2) * vecSqNorm (S ℓ) :=
        mul_le_mul_of_nonneg_left hsub_norm (sq_nonneg _)
    _ = ((S iStar j) ^ 2 * vecSqNorm (S ℓ)) / ((q : ℝ) ^ 2 * (S ℓ j) ^ 2) := by
        rw [div_pow, neg_sq, mul_pow, div_mul_eq_mul_div]
    _ ≤ ((S ℓ j) ^ 2 * vecSqNorm (S iStar)) / ((q : ℝ) ^ 2 * (S ℓ j) ^ 2) :=
        div_le_div_of_nonneg_right hcross (le_of_lt hden_pos)
    _ = vecSqNorm (S iStar) / ((q : ℝ) ^ 2) := by
        rw [mul_comm ((q : ℝ) ^ 2) ((S ℓ j) ^ 2), mul_div_mul_left _ _ (pow_ne_zero 2 hSℓ)]

private lemma treeCancel_inner_zero {n k q : ℕ} {S : Matrix (Fin n) (Fin k) ℝ}
    {V_G0 : Finset (Fin n)} {iStar : Fin n} {L : Fin k → Finset (Fin n)}
    (hq : 1 ≤ q) (hC4 : IsC4FreeRows S V_G0) (hiStar : iStar ∈ V_G0)
    (hL : ∀ j ∈ rowSupport S iStar, L j ⊆ V_G0 \ {iStar} ∧ (L j).card = q ∧
      ∀ ℓ ∈ L j, j ∈ rowSupport S ℓ ∧ relWeight S iStar j ≤ relWeight S ℓ j)
    {c : Fin k} (hc : c ∈ rowSupport S iStar) :
    (S.transpose.mulVec (treeCancelVec S iStar q L)) c = 0 := by
  rw [mulVec_treeCancelVec_eq S V_G0 iStar L (fun j hj => (hL j hj).1) c]
  have hsingle :
      (∑ j ∈ rowSupport S iStar, ∑ ℓ ∈ L j, S ℓ c * (-(S iStar j) / ((q : ℝ) * S ℓ j))) =
        ∑ ℓ ∈ L c, S ℓ c * (-(S iStar c) / ((q : ℝ) * S ℓ c)) := by
    refine Finset.sum_eq_single c (fun j hj hjc => ?_) (fun hnot => absurd hc hnot)
    refine Finset.sum_eq_zero fun ℓ hℓ => ?_
    have hℓ_sdiff := (hL j hj).1 hℓ
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hℓ_sdiff
    have hj_ℓ : j ∈ rowSupport S ℓ := ((hL j hj).2.2 ℓ hℓ).1
    have hc_not : c ∉ rowSupport S ℓ := by
      intro hc_ℓ
      exact hjc (c4Free_no_two_common_cols hC4 hiStar hℓ_sdiff.1 (Ne.symm hℓ_sdiff.2)
        hj hj_ℓ hc hc_ℓ)
    have hS0 : S ℓ c = 0 := not_not.mp ((mem_rowSupport_iff S ℓ c).not.mp hc_not)
    simp [hS0]
  rw [hsingle]
  have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.succ_le_iff.mp hq))
  have hinner :
      (∑ ℓ ∈ L c, S ℓ c * (-(S iStar c) / ((q : ℝ) * S ℓ c))) =
        ∑ _ℓ ∈ L c, (-(S iStar c) / (q : ℝ)) := by
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hSℓ : S ℓ c ≠ 0 := (mem_rowSupport_iff S ℓ c).mp (((hL c hc).2.2 ℓ hℓ).1)
    rw [← mul_div_assoc, mul_comm (q : ℝ) (S ℓ c), mul_div_mul_left _ _ hSℓ]
  rw [hinner, Finset.sum_const, nsmul_eq_mul, (hL c hc).2.1, mul_div_cancel₀ _ hq_ne]
  ring

private lemma treeCancel_outer_energy {n k q : ℕ} {S : Matrix (Fin n) (Fin k) ℝ}
    {V_G0 : Finset (Fin n)} {iStar : Fin n} {L : Fin k → Finset (Fin n)}
    (hq : 1 ≤ q)
    (hL : ∀ j ∈ rowSupport S iStar, L j ⊆ V_G0 \ {iStar} ∧ (L j).card = q ∧
      ∀ ℓ ∈ L j, j ∈ rowSupport S ℓ ∧ relWeight S iStar j ≤ relWeight S ℓ j)
    (hDisj : ∀ j₁ ∈ rowSupport S iStar, ∀ ℓ₁ ∈ L j₁, ∀ j₂ ∈ rowSupport S iStar, ∀ ℓ₂ ∈ L j₂,
      (j₁, ℓ₁) ≠ (j₂, ℓ₂) →
        Disjoint (rowSupport S ℓ₁ \ {j₁}) (rowSupport S ℓ₂ \ {j₂})) :
    (∑ c ∈ (rowSupport S iStar)ᶜ,
        ((S.transpose.mulVec (treeCancelVec S iStar q L)) c) ^ 2) ≤
      ((rowSupport S iStar).card : ℝ) * vecSqNorm (S iStar) / (q : ℝ) := by
  let J := rowSupport S iStar
  have hpyth :
      ∀ c ∈ Jᶜ, ((S.transpose.mulVec (treeCancelVec S iStar q L)) c) ^ 2 =
        ∑ j ∈ J, ∑ ℓ ∈ L j, (S ℓ c * (-(S iStar j) / ((q : ℝ) * S ℓ j))) ^ 2 := by
    intro c hc
    rw [mulVec_treeCancelVec_eq S V_G0 iStar L (fun j hj => (hL j hj).1) c]
    have hc_not : c ∉ rowSupport S iStar := Finset.mem_compl.mp hc
    have hS0 : S iStar c = 0 := not_not.mp ((mem_rowSupport_iff S iStar c).not.mp hc_not)
    rw [hS0, zero_add, Finset.sum_sigma' J L]
    rw [sq_sum_eq_sum_sq_of_at_most_one_ne_zero]
    · rw [Finset.sum_sigma J L]
    · intro p₁ hp₁ p₂ hp₂ hf₁ hf₂
      rcases Finset.mem_sigma.mp hp₁ with ⟨hj₁, hℓ₁⟩
      rcases Finset.mem_sigma.mp hp₂ with ⟨hj₂, hℓ₂⟩
      have hS₁ : S p₁.2 c ≠ 0 := left_ne_zero_of_mul hf₁
      have hS₂ : S p₂.2 c ≠ 0 := left_ne_zero_of_mul hf₂
      have hc₁ : c ∈ rowSupport S p₁.2 \ {p₁.1} := by
        refine Finset.mem_sdiff.mpr ⟨(mem_rowSupport_iff S p₁.2 c).mpr hS₁, ?_⟩
        exact Finset.notMem_singleton.mpr fun hcj => hc_not (hcj ▸ hj₁)
      have hc₂ : c ∈ rowSupport S p₂.2 \ {p₂.1} := by
        refine Finset.mem_sdiff.mpr ⟨(mem_rowSupport_iff S p₂.2 c).mpr hS₂, ?_⟩
        exact Finset.notMem_singleton.mpr fun hcj => hc_not (hcj ▸ hj₂)
      by_contra hp_ne
      have hpair_ne : (p₁.1, p₁.2) ≠ (p₂.1, p₂.2) := by
        intro heq
        rcases p₁ with ⟨j₁, ℓ₁⟩
        rcases p₂ with ⟨j₂, ℓ₂⟩
        cases heq
        exact hp_ne rfl
      exact Finset.disjoint_left.mp (hDisj p₁.1 hj₁ p₁.2 hℓ₁ p₂.1 hj₂ p₂.2 hℓ₂ hpair_ne) hc₁ hc₂
  have hswap :
      (∑ c ∈ Jᶜ, ((S.transpose.mulVec (treeCancelVec S iStar q L)) c) ^ 2) =
        ∑ j ∈ J, ∑ ℓ ∈ L j, ∑ c ∈ Jᶜ, (S ℓ c * (-(S iStar j) / ((q : ℝ) * S ℓ j))) ^ 2 := by
    rw [Finset.sum_congr rfl hpyth, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Finset.sum_comm
  rw [hswap]
  have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.succ_le_iff.mp hq))
  have hbranch :
      ∀ j ∈ J, (∑ ℓ ∈ L j, ∑ c ∈ Jᶜ, (S ℓ c * (-(S iStar j) / ((q : ℝ) * S ℓ j))) ^ 2) ≤
        vecSqNorm (S iStar) / (q : ℝ) := by
    intro j hj
    calc
      (∑ ℓ ∈ L j, ∑ c ∈ Jᶜ, (S ℓ c * (-(S iStar j) / ((q : ℝ) * S ℓ j))) ^ 2)
        ≤ ∑ _ℓ ∈ L j, (vecSqNorm (S iStar) / ((q : ℝ) ^ 2)) := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          exact leaf_outer_energy_le hq hj (((hL j hj).2.2 ℓ hℓ).1) (((hL j hj).2.2 ℓ hℓ).2)
      _ = vecSqNorm (S iStar) / (q : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, (hL j hj).2.1, sq, ← mul_div_assoc,
            mul_div_mul_left _ _ hq_ne]
  calc
    (∑ j ∈ J, ∑ ℓ ∈ L j, ∑ c ∈ Jᶜ, (S ℓ c * (-(S iStar j) / ((q : ℝ) * S ℓ j))) ^ 2)
      ≤ ∑ _j ∈ J, (vecSqNorm (S iStar) / (q : ℝ)) := Finset.sum_le_sum hbranch
    _ = (J.card : ℝ) * vecSqNorm (S iStar) / (q : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_div_assoc]

/-- **Lemma 9.1 (Single-tree inner cancellation and outer energy bound, p. 40).** -/
theorem lemma_9_1_TreeCancellation : Lemma_9_1_TreeCancellation := by
  intro n k _ζ q S V_G0 iStar L hq hC4 hiStar _hζ hL hDisj
  exact ⟨fun j hj => treeCancel_inner_zero hq hC4 hiStar hL hj,
    treeCancel_outer_energy hq hL hDisj⟩

private lemma same_branch_outer_disjoint {n k : ℕ} {S : Matrix (Fin n) (Fin k) ℝ}
    {V_G0 : Finset (Fin n)} (hC4 : IsC4FreeRows S V_G0)
    {j : Fin k} {ℓ₁ ℓ₂ : Fin n}
    (hℓ₁_VG0 : ℓ₁ ∈ V_G0) (hℓ₂_VG0 : ℓ₂ ∈ V_G0) (hℓ_ne : ℓ₁ ≠ ℓ₂)
    (hj₁ : j ∈ rowSupport S ℓ₁) (hj₂ : j ∈ rowSupport S ℓ₂) :
    Disjoint (rowSupport S ℓ₁ \ {j}) (rowSupport S ℓ₂ \ {j}) := by
  refine Finset.disjoint_left.mpr fun c hc₁ hc₂ => ?_
  rcases Finset.mem_sdiff.mp hc₁ with ⟨hc₁_supp, hc_ne⟩
  rcases Finset.mem_sdiff.mp hc₂ with ⟨hc₂_supp, _⟩
  have hcj : c ≠ j := Finset.notMem_singleton.mp hc_ne
  exact hℓ_ne (c4Free_eq_row_of_two_common_cols hC4 hℓ₁_VG0 hℓ₂_VG0 hcj
    hc₁_supp hc₂_supp hj₁ hj₂)

private lemma branch_fiber_card_le_one {n k : ℕ} {S : Matrix (Fin n) (Fin k) ℝ}
    {V_G0 : Finset (Fin n)} (hC4 : IsC4FreeRows S V_G0)
    {Fj : Finset (Fin n)} {j : Fin k}
    (hFj_VG0 : ∀ ℓ ∈ Fj, ℓ ∈ V_G0) (hFj_col : ∀ ℓ ∈ Fj, j ∈ rowSupport S ℓ) (c : Fin k)
    [DecidablePred (fun ℓ => c ∈ rowSupport S ℓ \ {j})] :
    (Fj.filter (fun ℓ => c ∈ rowSupport S ℓ \ {j})).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun ℓ₁ h₁ ℓ₂ h₂ => ?_
  rcases Finset.mem_filter.mp h₁ with ⟨hℓ₁F, hc₁⟩
  rcases Finset.mem_filter.mp h₂ with ⟨hℓ₂F, hc₂⟩
  by_contra hne
  exact Finset.disjoint_left.mp
    (same_branch_outer_disjoint hC4 (hFj_VG0 ℓ₁ hℓ₁F) (hFj_VG0 ℓ₂ hℓ₂F) hne
      (hFj_col ℓ₁ hℓ₁F) (hFj_col ℓ₂ hℓ₂F)) hc₁ hc₂

private lemma occupied_outer_card_le {n k ζ q : ℕ}
    {S : Matrix (Fin n) (Fin k) ℝ} {V_G0 : Finset (Fin n)} {iStar : Fin n}
    {F L' : Fin k → Finset (Fin n)}
    (hSparse : ∀ i ∈ V_G0, (rowSupport S i).card ≤ ζ)
    (hiStar : iStar ∈ V_G0)
    (hF : ∀ j ∈ rowSupport S iStar, F j ⊆ V_G0 \ {iStar} ∧
      (∀ ℓ ∈ F j, j ∈ rowSupport S ℓ) ∧
      q + q * (ζ - 1) ^ 2 ≤ (F j).card)
    {jStar : Fin k} {J' : Finset (Fin k)}
    (hjStar_notMem : jStar ∉ J') (hins : insert jStar J' ⊆ rowSupport S iStar)
    (hL'_card : ∀ j ∈ J', L' j ⊆ F j ∧ (L' j).card = q) :
    (J'.biUnion (fun j => (L' j).biUnion (fun ℓ => rowSupport S ℓ \ {j}))).card ≤
      q * (ζ - 1) ^ 2 := by
  have hJ_sub : J' ⊆ rowSupport S iStar := (Finset.subset_insert jStar J').trans hins
  have hJ'_card : J'.card ≤ ζ - 1 := by
    have h1 : (insert jStar J').card ≤ (rowSupport S iStar).card := Finset.card_le_card hins
    have h2 : (rowSupport S iStar).card ≤ ζ := hSparse iStar hiStar
    rw [Finset.card_insert_of_notMem hjStar_notMem] at h1
    omega
  have hbranch_card :
      ∀ j ∈ J', ((L' j).biUnion (fun ℓ => rowSupport S ℓ \ {j})).card ≤ q * (ζ - 1) := by
    intro j hj
    have hj_mem : j ∈ rowSupport S iStar := hJ_sub hj
    have hleaf_card : ∀ ℓ ∈ L' j, (rowSupport S ℓ \ {j}).card ≤ ζ - 1 := by
      intro ℓ hℓ
      have hℓF : ℓ ∈ F j := (hL'_card j hj).1 hℓ
      have hℓ_VG0 : ℓ ∈ V_G0 := (Finset.mem_sdiff.mp ((hF j hj_mem).1 hℓF)).1
      have hj_ℓ : j ∈ rowSupport S ℓ := (hF j hj_mem).2.1 ℓ hℓF
      have hcs : (rowSupport S ℓ \ {j}).card = (rowSupport S ℓ).card - 1 := by
        rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hj_ℓ),
          Finset.card_singleton]
      have hsp : (rowSupport S ℓ).card ≤ ζ := hSparse ℓ hℓ_VG0
      omega
    calc
      ((L' j).biUnion (fun ℓ => rowSupport S ℓ \ {j})).card
        ≤ (L' j).card * (ζ - 1) := Finset.card_biUnion_le_card_mul _ _ _ hleaf_card
      _ = q * (ζ - 1) := by rw [(hL'_card j hj).2]
  calc
    (J'.biUnion (fun j => (L' j).biUnion (fun ℓ => rowSupport S ℓ \ {j}))).card
      ≤ J'.card * (q * (ζ - 1)) := Finset.card_biUnion_le_card_mul _ _ _ hbranch_card
    _ ≤ (ζ - 1) * (q * (ζ - 1)) := Nat.mul_le_mul_right (q * (ζ - 1)) hJ'_card
    _ = q * (ζ - 1) ^ 2 := by ring

private lemma greedy_select_on_subset {n k ζ q : ℕ}
    {S : Matrix (Fin n) (Fin k) ℝ} {V_G0 : Finset (Fin n)} {iStar : Fin n}
    {F : Fin k → Finset (Fin n)}
    (hC4 : IsC4FreeRows S V_G0)
    (hSparse : ∀ i ∈ V_G0, (rowSupport S i).card ≤ ζ)
    (hiStar : iStar ∈ V_G0)
    (hF : ∀ j ∈ rowSupport S iStar, F j ⊆ V_G0 \ {iStar} ∧
      (∀ ℓ ∈ F j, j ∈ rowSupport S ℓ) ∧
      q + q * (ζ - 1) ^ 2 ≤ (F j).card)
    (J : Finset (Fin k)) (hJ : J ⊆ rowSupport S iStar) :
    ∃ L : Fin k → Finset (Fin n),
      (∀ j ∈ J, L j ⊆ F j ∧ (L j).card = q) ∧
        ∀ j₁ ∈ J, ∀ ℓ₁ ∈ L j₁, ∀ j₂ ∈ J, ∀ ℓ₂ ∈ L j₂,
          (j₁, ℓ₁) ≠ (j₂, ℓ₂) →
            Disjoint (rowSupport S ℓ₁ \ {j₁}) (rowSupport S ℓ₂ \ {j₂}) := by
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => ∅, ?_, ?_⟩
    · intro j hj; exact absurd hj (Finset.notMem_empty j)
    · intro j₁ hj₁; exact absurd hj₁ (Finset.notMem_empty j₁)
  | @insert jStar J' hjStar_notMem ih =>
    classical
    have hJ'_sub : J' ⊆ rowSupport S iStar := (Finset.subset_insert jStar J').trans hJ
    obtain ⟨L', hL'_card, hL'_disj⟩ := ih hJ'_sub
    have hjStar_mem : jStar ∈ rowSupport S iStar := hJ (Finset.mem_insert_self jStar J')
    let C_occ : Finset (Fin k) :=
      J'.biUnion (fun j => (L' j).biUnion (fun ℓ => rowSupport S ℓ \ {j}))
    have hC_occ_card : C_occ.card ≤ q * (ζ - 1) ^ 2 :=
      occupied_outer_card_le hSparse hiStar hF hjStar_notMem hJ hL'_card
    let Good : Finset (Fin n) :=
      (F jStar).filter (fun ℓ => Disjoint (rowSupport S ℓ \ {jStar}) C_occ)
    let Bad : Finset (Fin n) :=
      (F jStar).filter (fun ℓ => ¬ Disjoint (rowSupport S ℓ \ {jStar}) C_occ)
    let fiber : Fin k → Finset (Fin n) :=
      fun c => (F jStar).filter (fun ℓ => c ∈ rowSupport S ℓ \ {jStar})
    have hBad_sub : Bad ⊆ C_occ.biUnion fiber := by
      intro ℓ hℓ
      rcases Finset.mem_filter.mp hℓ with ⟨hℓF, hnot⟩
      obtain ⟨c, hc_sdiff, hc_occ⟩ := Finset.not_disjoint_iff.mp hnot
      exact Finset.mem_biUnion.mpr ⟨c, hc_occ, Finset.mem_filter.mpr ⟨hℓF, hc_sdiff⟩⟩
    have hFj_VG0 : ∀ ℓ ∈ F jStar, ℓ ∈ V_G0 :=
      fun ℓ hℓ => (Finset.mem_sdiff.mp ((hF jStar hjStar_mem).1 hℓ)).1
    have hFj_col : ∀ ℓ ∈ F jStar, jStar ∈ rowSupport S ℓ := (hF jStar hjStar_mem).2.1
    have hBad_card : Bad.card ≤ q * (ζ - 1) ^ 2 := by
      calc
        Bad.card ≤ (C_occ.biUnion fiber).card := Finset.card_le_card hBad_sub
        _ ≤ C_occ.card * 1 :=
            Finset.card_biUnion_le_card_mul C_occ fiber 1
              (fun c _ => branch_fiber_card_le_one hC4 hFj_VG0 hFj_col c)
        _ = C_occ.card := Nat.mul_one _
        _ ≤ q * (ζ - 1) ^ 2 := hC_occ_card
    have hGood_card : q ≤ Good.card := by
      have hpart : Good.card + Bad.card = (F jStar).card :=
        Finset.card_filter_add_card_filter_not
          (fun ℓ => Disjoint (rowSupport S ℓ \ {jStar}) C_occ)
      have hF_lb : q + q * (ζ - 1) ^ 2 ≤ (F jStar).card := (hF jStar hjStar_mem).2.2
      omega
    obtain ⟨L_star, hL_star_sub, hL_star_card⟩ := Finset.exists_subset_card_eq hGood_card
    let L : Fin k → Finset (Fin n) := fun j => if j = jStar then L_star else L' j
    refine ⟨L, ?_, ?_⟩
    · intro j hj
      by_cases hj_eq : j = jStar
      · have hLj : L j = L_star := if_pos hj_eq
        rw [hLj, hj_eq]
        exact ⟨hL_star_sub.trans (Finset.filter_subset _ _), hL_star_card⟩
      · have hj' : j ∈ J' := Finset.mem_of_mem_insert_of_ne hj hj_eq
        have hLj : L j = L' j := if_neg hj_eq
        rw [hLj]
        exact hL'_card j hj'
    · intro j₁ hj₁ ℓ₁ hℓ₁ j₂ hj₂ ℓ₂ hℓ₂ hne
      have hsub_occ : ∀ j ∈ J', ∀ ℓ ∈ L' j, rowSupport S ℓ \ {j} ⊆ C_occ := by
        intro j hj ℓ hℓ
        exact (Finset.subset_biUnion_of_mem (fun m => rowSupport S m \ {j}) hℓ).trans
          (Finset.subset_biUnion_of_mem
            (fun t => (L' t).biUnion (fun m => rowSupport S m \ {t})) hj)
      by_cases hj₁_eq : j₁ = jStar
      · have hL₁ : L j₁ = L_star := if_pos hj₁_eq
        rw [hL₁] at hℓ₁
        rcases Finset.mem_filter.mp (hL_star_sub hℓ₁) with ⟨hℓ₁F, hℓ₁_disj⟩
        by_cases hj₂_eq : j₂ = jStar
        · have hL₂ : L j₂ = L_star := if_pos hj₂_eq
          rw [hL₂] at hℓ₂
          rcases Finset.mem_filter.mp (hL_star_sub hℓ₂) with ⟨hℓ₂F, _⟩
          have hℓ_ne : ℓ₁ ≠ ℓ₂ := by
            intro heq
            apply hne
            rw [hj₁_eq, hj₂_eq, heq]
          rw [hj₁_eq, hj₂_eq]
          exact same_branch_outer_disjoint hC4 (hFj_VG0 ℓ₁ hℓ₁F) (hFj_VG0 ℓ₂ hℓ₂F) hℓ_ne
            (hFj_col ℓ₁ hℓ₁F) (hFj_col ℓ₂ hℓ₂F)
        · have hj₂' : j₂ ∈ J' := Finset.mem_of_mem_insert_of_ne hj₂ hj₂_eq
          have hL₂ : L j₂ = L' j₂ := if_neg hj₂_eq
          rw [hL₂] at hℓ₂
          rw [hj₁_eq]
          exact hℓ₁_disj.mono_right (hsub_occ j₂ hj₂' ℓ₂ hℓ₂)
      · have hj₁' : j₁ ∈ J' := Finset.mem_of_mem_insert_of_ne hj₁ hj₁_eq
        have hL₁ : L j₁ = L' j₁ := if_neg hj₁_eq
        rw [hL₁] at hℓ₁
        by_cases hj₂_eq : j₂ = jStar
        · have hL₂ : L j₂ = L_star := if_pos hj₂_eq
          rw [hL₂] at hℓ₂
          rcases Finset.mem_filter.mp (hL_star_sub hℓ₂) with ⟨_, hℓ₂_disj⟩
          rw [hj₂_eq]
          exact (hℓ₂_disj.mono_right (hsub_occ j₁ hj₁' ℓ₁ hℓ₁)).symm
        · have hj₂' : j₂ ∈ J' := Finset.mem_of_mem_insert_of_ne hj₂ hj₂_eq
          have hL₂ : L j₂ = L' j₂ := if_neg hj₂_eq
          rw [hL₂] at hℓ₂
          exact hL'_disj j₁ hj₁' ℓ₁ hℓ₁ j₂ hj₂' ℓ₂ hℓ₂ hne

/-- **Lemma 9.2 (Greedy outer-disjoint leaf selection for a single tree, p. 41).** -/
theorem lemma_9_2_SingleTreeDisjointLeaves : Lemma_9_2_SingleTreeDisjointLeaves := by
  intro n k ζ q S V_G0 iStar F _hζ1 hC4 hSparse hiStar hF
  exact greedy_select_on_subset hC4 hSparse hiStar hF (rowSupport S iStar) Finset.Subset.rfl

end Osi.LowerBound
