import Osi.Spec
import Osi.LowerBound.C4Subgraph
import Osi.LowerBound.TreeCancel
import Osi.LowerBound.TuranCenters

/-!
# Section 9.4: Hall's Marriage Theorem, Disjoint Leaf Reservoirs, and Witness Forest

Proves `Lemma_9_5_HallMarriage`, `Lemma_9_6_DisjointLeafReservoirs`, and
`Theorem_9_7_WitnessForest`.
-/

namespace Osi.LowerBound

open Osi.Spec

/-- **Lemma 9.5 (Hall's Marriage Theorem for finite bipartite graphs, p. 43).** -/
theorem lemma_9_5_HallMarriage : Lemma_9_5_HallMarriage := by
  intro m n R
  classical
  let t : Fin m → Finset (Fin n) := fun u => Finset.univ.filter (fun v => R u v)
  have hmem : ∀ (u : Fin m) (v : Fin n), R u v ↔ v ∈ t u := by
    intro u v
    simp [t]
  have hcard : ∀ A : Finset (Fin m),
      ((Set.toFinite {v : Fin n | ∃ u ∈ A, R u v}).toFinset).card = (A.biUnion t).card := by
    intro A
    congr 1
    ext v
    simp [t]
  refine Iff.trans ?_ (Iff.trans (Finset.all_card_le_biUnion_card_iff_existsInjective' t).symm ?_)
  · constructor
    · rintro ⟨f, hfinj, hf⟩
      exact ⟨f, hfinj, fun u => (hmem u (f u)).mp (hf u)⟩
    · rintro ⟨f, hfinj, hf⟩
      exact ⟨f, hfinj, fun u => (hmem u (f u)).mpr (hf u)⟩
  · exact forall_congr' (fun A => by rw [hcard A])

/-- Double-counting verification of Hall's condition on the `L`-cloned left slot graph
`↥J_branch × Fin L` for `lemma_9_6_DisjointLeafReservoirs`. -/
private lemma hall_cond_cloned_reservoirs {n k' ζ L D : ℕ}
    (J_branch : Finset (Fin k')) (F : Fin k' → Finset (Fin n))
    (hζ : 1 ≤ ζ) (hL : 0 < L) (hD : ζ * L ≤ D)
    (hcard : ∀ j' ∈ J_branch, D ≤ (F j').card)
    (hmult : ∀ ℓ : Fin n,
      ((Set.toFinite {j' : Fin k' | j' ∈ J_branch ∧ ℓ ∈ F j'}).toFinset).card ≤ ζ)
    (A : Finset (↥J_branch × Fin L)) :
    A.card ≤ (A.biUnion (fun p => F p.1.1)).card := by
  let t : ↥J_branch × Fin L → Finset (Fin n) := fun p => F p.1.1
  let N : Finset (Fin n) := A.biUnion t
  have hlow : A.card * (ζ * L) ≤ ∑ p ∈ A, (t p).card := by
    calc A.card * (ζ * L)
        = ∑ _p ∈ A, (ζ * L) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ p ∈ A, (t p).card :=
          Finset.sum_le_sum (fun p _ => le_trans hD (hcard p.1.1 p.1.2))
  have hswap : ∑ p ∈ A, (t p).card =
      ∑ ℓ ∈ N, (A.filter (fun p => ℓ ∈ F p.1.1)).card := by
    have hp_eq : ∀ p ∈ A, (t p).card = ∑ ℓ ∈ N, (if ℓ ∈ F p.1.1 then 1 else 0) := by
      intro p hp
      have hsub : t p ⊆ N := Finset.subset_biUnion_of_mem t hp
      rw [← Finset.card_filter]
      congr 1
      ext ℓ
      simp only [Finset.mem_filter]
      exact ⟨fun hℓ => ⟨hsub hℓ, hℓ⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl hp_eq, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [Finset.card_filter]
  have hdeg : ∀ ℓ : Fin n, (A.filter (fun p => ℓ ∈ F p.1.1)).card ≤ ζ * L := by
    intro ℓ
    let J_ℓ : Finset ↥J_branch :=
      (Finset.univ : Finset ↥J_branch).filter (fun j' => ℓ ∈ F j'.1)
    have hsubA : A.filter (fun p => ℓ ∈ F p.1.1) ⊆
        J_ℓ ×ˢ (Finset.univ : Finset (Fin L)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_product]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, Finset.mem_univ _⟩
    have hJ_card : J_ℓ.card ≤ ζ := by
      have himg : J_ℓ.image Subtype.val ⊆
          (Set.toFinite {j' : Fin k' | j' ∈ J_branch ∧ ℓ ∈ F j'}).toFinset := by
        intro j' hj'
        rcases Finset.mem_image.mp hj' with ⟨u, hu, rfl⟩
        rw [Set.Finite.mem_toFinset]
        exact ⟨u.2, (Finset.mem_filter.mp hu).2⟩
      calc J_ℓ.card
          = (J_ℓ.image Subtype.val).card :=
              (Finset.card_image_of_injective J_ℓ Subtype.val_injective).symm
        _ ≤ ((Set.toFinite {j' : Fin k' | j' ∈ J_branch ∧ ℓ ∈ F j'}).toFinset).card :=
              Finset.card_le_card himg
        _ ≤ ζ := hmult ℓ
    calc (A.filter (fun p => ℓ ∈ F p.1.1)).card
        ≤ (J_ℓ ×ˢ (Finset.univ : Finset (Fin L))).card := Finset.card_le_card hsubA
      _ = J_ℓ.card * L := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      _ ≤ ζ * L := Nat.mul_le_mul_right L hJ_card
  have hhigh : ∑ p ∈ A, (t p).card ≤ N.card * (ζ * L) := by
    rw [hswap]
    calc ∑ ℓ ∈ N, (A.filter (fun p => ℓ ∈ F p.1.1)).card
        ≤ ∑ _ℓ ∈ N, (ζ * L) := Finset.sum_le_sum (fun ℓ _ => hdeg ℓ)
      _ = N.card * (ζ * L) := by rw [Finset.sum_const, smul_eq_mul]
  exact Nat.le_of_mul_le_mul_right (le_trans hlow hhigh) (Nat.mul_pos hζ hL)

/-- **Lemma 9.6 (Simultaneous allocation of disjoint leaf reservoirs, p. 43).** -/
theorem lemma_9_6_DisjointLeafReservoirs : Lemma_9_6_DisjointLeafReservoirs := by
  intro n k' ζ L D J_branch F hζ hD hcard hmult
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · refine ⟨fun _ => ∅, ?_, ?_⟩
    · intro j' _
      exact ⟨Finset.empty_subset _, Finset.card_empty⟩
    · intro _ _ _ _ _
      exact Finset.disjoint_empty_left _
  · let t : ↥J_branch × Fin L → Finset (Fin n) := fun p => F p.1.1
    have hHall : ∀ A : Finset (↥J_branch × Fin L), A.card ≤ (A.biUnion t).card :=
      hall_cond_cloned_reservoirs J_branch F hζ hL hD hcard hmult
    rcases (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall with
      ⟨f, hf_inj, hf_mem⟩
    let R_res : Fin k' → Finset (Fin n) := fun j' =>
      if hj : j' ∈ J_branch then
        (Finset.univ : Finset (Fin L)).image (fun s => f (⟨j', hj⟩, s))
      else ∅
    refine ⟨R_res, ?_, ?_⟩
    · intro j' hj'
      have hR_eq : R_res j' =
          (Finset.univ : Finset (Fin L)).image (fun s => f (⟨j', hj'⟩, s)) :=
        dif_pos hj'
      rw [hR_eq]
      refine ⟨?_, ?_⟩
      · intro ℓ hℓ
        rcases Finset.mem_image.mp hℓ with ⟨s, _, rfl⟩
        exact hf_mem (⟨j', hj'⟩, s)
      · have hinj_s : Function.Injective (fun s : Fin L => f (⟨j', hj'⟩, s)) := by
          intro s₁ s₂ hs
          exact congrArg Prod.snd (hf_inj hs)
        rw [Finset.card_image_of_injective _ hinj_s, Finset.card_univ, Fintype.card_fin]
    · intro j₁' hj₁' j₂' hj₂' hne
      rw [show R_res j₁' = (Finset.univ : Finset (Fin L)).image (fun s => f (⟨j₁', hj₁'⟩, s))
            from dif_pos hj₁',
          show R_res j₂' = (Finset.univ : Finset (Fin L)).image (fun s => f (⟨j₂', hj₂'⟩, s))
            from dif_pos hj₂',
          Finset.disjoint_left]
      intro ℓ hℓ₁ hℓ₂
      rcases Finset.mem_image.mp hℓ₁ with ⟨s₁, _, rfl⟩
      rcases Finset.mem_image.mp hℓ₂ with ⟨s₂, _, heq⟩
      have hpair := hf_inj heq
      exact hne (congrArg (fun p => p.1.1) hpair.symm)

/-- Padding `T` pairwise disjoint subsets `A s ⊆ U` of size `≤ B` inside a universe `U` of size
`≥ T * B` to pairwise disjoint subsets `V s ⊆ U` of exact size `B` with `A s ⊆ V s`. -/
private lemma pad_disjoint_subsets {α : Type*} [DecidableEq α]
    (U : Finset α) (T B : ℕ) (A : Fin T → Finset α)
    (hA_sub : ∀ s : Fin T, A s ⊆ U)
    (hA_card : ∀ s : Fin T, (A s).card ≤ B)
    (hA_disj : ∀ s u : Fin T, s ≠ u → Disjoint (A s) (A u))
    (hU_card : T * B ≤ U.card) :
    ∃ V : Fin T → Finset α,
      (∀ s : Fin T, A s ⊆ V s ∧ V s ⊆ U ∧ (V s).card = B) ∧
      (∀ s u : Fin T, s ≠ u → Disjoint (V s) (V u)) := by
  induction T generalizing U with
  | zero =>
    exact ⟨fun s => s.elim0, fun s => s.elim0, fun s => s.elim0⟩
  | succ T ih =>
    let tailUnion : Finset α :=
      (Finset.univ : Finset (Fin T)).biUnion (fun s => A s.succ)
    have htail_sub : tailUnion ⊆ U :=
      Finset.biUnion_subset.mpr (fun s _ => hA_sub s.succ)
    have htail_card : tailUnion.card ≤ T * B := by
      calc tailUnion.card
          ≤ ∑ s : Fin T, (A s.succ).card := Finset.card_biUnion_le
        _ ≤ ∑ _s : Fin T, B := Finset.sum_le_sum (fun s _ => hA_card s.succ)
        _ = T * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    let pool0 : Finset α := U \ tailUnion
    have hA0_disj_tail : Disjoint (A 0) tailUnion := by
      rw [Finset.disjoint_biUnion_right]
      intro s _
      exact hA_disj 0 s.succ (Fin.succ_ne_zero s).symm
    have hA0_pool : A 0 ⊆ pool0 :=
      Finset.subset_sdiff.mpr ⟨hA_sub 0, hA0_disj_tail⟩
    have hpool_card : B ≤ pool0.card := by
      have h1 : pool0.card + tailUnion.card = U.card :=
        Finset.card_sdiff_add_card_eq_card htail_sub
      have h2 : T * B + B ≤ U.card := by simpa [Nat.succ_mul] using hU_card
      omega
    have hrem_card : B - (A 0).card ≤ (pool0 \ A 0).card := by
      have h1 : (pool0 \ A 0).card + (A 0).card = pool0.card :=
        Finset.card_sdiff_add_card_eq_card hA0_pool
      omega
    rcases Finset.exists_subset_card_eq hrem_card with ⟨P0, hP0_sub, hP0_card⟩
    let V0 : Finset α := A 0 ∪ P0
    have hdisj_P0 : Disjoint (A 0) P0 :=
      Disjoint.mono_right hP0_sub disjoint_sdiff_self_right
    have hV0_card : V0.card = B := by
      have hc : V0.card = (A 0).card + P0.card := Finset.card_union_of_disjoint hdisj_P0
      have hA0_le := hA_card 0
      omega
    have hV0_pool : V0 ⊆ pool0 :=
      Finset.union_subset hA0_pool (le_trans hP0_sub Finset.sdiff_subset)
    have hV0_sub : V0 ⊆ U := le_trans hV0_pool Finset.sdiff_subset
    let U' : Finset α := U \ V0
    have hU'_card : T * B ≤ U'.card := by
      have h1 : U'.card + V0.card = U.card := Finset.card_sdiff_add_card_eq_card hV0_sub
      have h2 : T * B + B ≤ U.card := by simpa [Nat.succ_mul] using hU_card
      omega
    have hA'_sub : ∀ s : Fin T, A s.succ ⊆ U' := by
      intro s
      refine Finset.subset_sdiff.mpr ⟨hA_sub s.succ, ?_⟩
      have hs_tail : A s.succ ⊆ tailUnion :=
        Finset.subset_biUnion_of_mem (fun t => A t.succ) (Finset.mem_univ s)
      exact Disjoint.mono hs_tail hV0_pool disjoint_sdiff_self_right
    have hA'_disj : ∀ s u : Fin T, s ≠ u → Disjoint (A s.succ) (A u.succ) :=
      fun s u hne => hA_disj s.succ u.succ (fun h => hne (Fin.succ_inj.mp h))
    rcases ih U' (fun s => A s.succ) hA'_sub (fun s => hA_card s.succ) hA'_disj hU'_card with
      ⟨V', hV'_prop, hV'_disj⟩
    refine ⟨Fin.cons V0 V', ?_, ?_⟩
    · intro s
      refine Fin.cases ?_ ?_ s
      · simp only [Fin.cons_zero]
        exact ⟨Finset.subset_union_left, hV0_sub, hV0_card⟩
      · intro s'
        simp only [Fin.cons_succ]
        exact ⟨(hV'_prop s').1, le_trans (hV'_prop s').2.1 Finset.sdiff_subset,
          (hV'_prop s').2.2⟩
    · intro s u
      refine Fin.cases ?_ ?_ s
      · refine Fin.cases ?_ ?_ u
        · intro hne
          exact False.elim (hne rfl)
        · intro u' _
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact Disjoint.mono_right (hV'_prop u').2.1 disjoint_sdiff_self_right
      · intro s'
        refine Fin.cases ?_ ?_ u
        · intro _
          simp only [Fin.cons_succ, Fin.cons_zero]
          exact (Disjoint.mono_right (hV'_prop s').2.1 disjoint_sdiff_self_right).symm
        · intro u' hne
          simp only [Fin.cons_succ]
          exact hV'_disj s' u' (fun h => hne (congrArg Fin.succ h))

/-- Quantitative parameter bounds for `theorem_9_7_WitnessForest`: proves `1 ≤ T`,
`c_T * r / ζ^5 ≤ T`, `T ≤ I_center.card`, `1 ≤ q`, and `T * (1 + ζ * q) ≤ V_G0.card`. -/
private lemma witness_forest_param_bounds
    {c_T₁ c_T C_samp₂ K C_samp α : ℝ} {k r ζ n₀ vg0_card icenter_card T q : ℕ}
    (hcT_pos : 0 < c_T) (hcT_le1 : c_T ≤ c_T₁) (hcT_le16 : c_T ≤ 1 / 16)
    (hCs2_pos : 0 < C_samp₂) (hcT_Cs2 : 1 ≤ c_T * C_samp₂) (hCs2_3000 : (3000 : ℝ) ≤ C_samp₂)
    (hK : 1 ≤ K) (hCsamp : C_samp₂ * K ^ 2 ≤ C_samp)
    (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (hr : 2 ≤ r) (hk_le : (k : ℝ) ≤ K * (r : ℝ)) (hζ : 2 ≤ ζ)
    (hn₀ : n₀ = Nat.ceil (C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α))
    (hT_def : T = Nat.ceil (c_T * (r : ℝ) / (ζ : ℝ) ^ 5))
    (hq_def : q = Nat.ceil (640 * (ζ : ℝ) / α))
    (hvg0_lo : (5 / 8 : ℝ) * (n₀ : ℝ) ≤ (vg0_card : ℝ))
    (hc4_pairs : 2 * vg0_card ≤ k * (k - 1))
    (hicenter : c_T₁ * (r : ℝ) / (ζ : ℝ) ^ 5 ≤ (icenter_card : ℝ)) :
    1 ≤ T ∧
      c_T * (r : ℝ) / (ζ : ℝ) ^ 5 ≤ (T : ℝ) ∧
      T ≤ icenter_card ∧
      1 ≤ q ∧
      T * (1 + ζ * q) ≤ vg0_card := by
  have hK_sq : 1 ≤ K ^ 2 := by nlinarith
  have hCsamp_ge_Cs2 : C_samp₂ ≤ C_samp := by
    calc C_samp₂ = C_samp₂ * 1 := (mul_one _).symm
      _ ≤ C_samp₂ * K ^ 2 := mul_le_mul_of_nonneg_left hK_sq hCs2_pos.le
      _ ≤ C_samp := hCsamp
  have hCsamp_3000 : (3000 : ℝ) ≤ C_samp := le_trans hCs2_3000 hCsamp_ge_Cs2
  have hr_real : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hζ_real : (2 : ℝ) ≤ (ζ : ℝ) := by exact_mod_cast hζ
  have hζ_pos : (0 : ℝ) < (ζ : ℝ) := by linarith
  have hζ5_pos : (0 : ℝ) < (ζ : ℝ) ^ 5 := pow_pos hζ_pos 5
  have hζ5_ge1 : (1 : ℝ) ≤ (ζ : ℝ) ^ 5 := one_le_pow₀ (by linarith)
  have hζ6_nonneg : (0 : ℝ) ≤ (ζ : ℝ) ^ 6 := pow_nonneg hζ_pos.le 6
  have hn₀_lo : C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α ≤ (n₀ : ℝ) := by
    rw [hn₀]
    exact Nat.le_ceil _
  have hn₀_lo_no_alpha : C_samp₂ * K ^ 2 * (r : ℝ) * (ζ : ℝ) ^ 6 ≤ (n₀ : ℝ) := by
    have hW_pos : 0 ≤ C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 :=
      mul_nonneg (mul_nonneg (le_trans hCs2_pos.le hCsamp_ge_Cs2) (by linarith)) hζ6_nonneg
    have hdiv : C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 ≤ C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α :=
      (le_div_iff₀ hα_pos).mpr (mul_le_of_le_one_right hW_pos hα_le)
    have hmul : C_samp₂ * K ^ 2 * (r : ℝ) * (ζ : ℝ) ^ 6 ≤
        C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCsamp (by linarith)) hζ6_nonneg
    exact le_trans hmul (le_trans hdiv hn₀_lo)
  have hvg0_up : 2 * (vg0_card : ℝ) ≤ K ^ 2 * (r : ℝ) ^ 2 := by
    have hnat : 2 * vg0_card ≤ k * k :=
      le_trans hc4_pairs (Nat.mul_le_mul_left k (Nat.sub_le k 1))
    have hreal : 2 * (vg0_card : ℝ) ≤ (k : ℝ) * (k : ℝ) := by exact_mod_cast hnat
    have hk_sq : (k : ℝ) * (k : ℝ) ≤ (K * (r : ℝ)) * (K * (r : ℝ)) :=
      mul_self_le_mul_self (Nat.cast_nonneg k) hk_le
    calc 2 * (vg0_card : ℝ)
        ≤ (K * (r : ℝ)) * (K * (r : ℝ)) := le_trans hreal hk_sq
      _ = K ^ 2 * (r : ℝ) ^ 2 := by ring
  have hr_lo : (5 / 2 : ℝ) * C_samp₂ * (ζ : ℝ) ^ 5 ≤ (r : ℝ) := by
    have hcomb : (K ^ 2 * (r : ℝ)) * ((5 / 4 : ℝ) * C_samp₂ * (ζ : ℝ) ^ 6) ≤
        (K ^ 2 * (r : ℝ)) * (r : ℝ) := by linarith
    have hK2r_pos : 0 < K ^ 2 * (r : ℝ) := mul_pos (by positivity) (by linarith)
    have hr6 : (5 / 4 : ℝ) * C_samp₂ * (ζ : ℝ) ^ 6 ≤ (r : ℝ) :=
      le_of_mul_le_mul_left hcomb hK2r_pos
    have hfactor : (5 / 2 : ℝ) ≤ (5 / 4 : ℝ) * (ζ : ℝ) := by linarith
    have hstep : (5 / 2 : ℝ) * C_samp₂ * (ζ : ℝ) ^ 5 ≤
        (5 / 4 : ℝ) * C_samp₂ * (ζ : ℝ) ^ 6 := by
      calc (5 / 2 : ℝ) * C_samp₂ * (ζ : ℝ) ^ 5
          = (5 / 2 : ℝ) * (C_samp₂ * (ζ : ℝ) ^ 5) := by ring
        _ ≤ ((5 / 4 : ℝ) * (ζ : ℝ)) * (C_samp₂ * (ζ : ℝ) ^ 5) :=
            mul_le_mul_of_nonneg_right hfactor (mul_nonneg hCs2_pos.le hζ5_pos.le)
        _ = (5 / 4 : ℝ) * C_samp₂ * (ζ : ℝ) ^ 6 := by ring
    exact le_trans hstep hr6
  have hX_ge1 : 1 ≤ c_T * (r : ℝ) / (ζ : ℝ) ^ 5 := by
    refine (le_div_iff₀ hζ5_pos).mpr ?_
    calc 1 * (ζ : ℝ) ^ 5
        = (ζ : ℝ) ^ 5 := one_mul _
      _ ≤ ((5 / 2 : ℝ) * (c_T * C_samp₂)) * (ζ : ℝ) ^ 5 :=
          le_mul_of_one_le_left hζ5_pos.le (by linarith)
      _ = c_T * ((5 / 2 : ℝ) * C_samp₂ * (ζ : ℝ) ^ 5) := by ring
      _ ≤ c_T * (r : ℝ) := mul_le_mul_of_nonneg_left hr_lo hcT_pos.le
  have hX_le_T : c_T * (r : ℝ) / (ζ : ℝ) ^ 5 ≤ (T : ℝ) := by
    rw [hT_def]
    exact Nat.le_ceil _
  have hT_ge1 : 1 ≤ T := by
    have : (1 : ℝ) ≤ (T : ℝ) := le_trans hX_ge1 hX_le_T
    exact_mod_cast this
  have hT_le_icenter : T ≤ icenter_card := by
    rw [hT_def]
    refine Nat.ceil_le.mpr ?_
    have hX_le1 : c_T * (r : ℝ) / (ζ : ℝ) ^ 5 ≤ c_T₁ * (r : ℝ) / (ζ : ℝ) ^ 5 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcT_le1 (by linarith)) hζ5_pos.le
    exact le_trans hX_le1 hicenter
  have hQ0_ge1 : 1 ≤ 640 * (ζ : ℝ) / α := (le_div_iff₀ hα_pos).mpr (by linarith)
  have hq_lo : 640 * (ζ : ℝ) / α ≤ (q : ℝ) := by
    rw [hq_def]
    exact Nat.le_ceil _
  have hq_ge1 : 1 ≤ q := by
    have : (1 : ℝ) ≤ (q : ℝ) := le_trans hQ0_ge1 hq_lo
    exact_mod_cast this
  have hTB_le : T * (1 + ζ * q) ≤ vg0_card := by
    have hT_up : (T : ℝ) ≤ (r : ℝ) := by
      have hX_nonneg : 0 ≤ c_T * (r : ℝ) / (ζ : ℝ) ^ 5 := le_trans zero_le_one hX_ge1
      have hceil : (T : ℝ) ≤ c_T * (r : ℝ) / (ζ : ℝ) ^ 5 + 1 := by
        rw [hT_def]
        exact (Nat.ceil_lt_add_one hX_nonneg).le
      have hX_up : c_T * (r : ℝ) / (ζ : ℝ) ^ 5 ≤ c_T * (r : ℝ) :=
        div_le_self (mul_nonneg hcT_pos.le (by linarith)) hζ5_ge1
      have hcr : 2 * (c_T * (r : ℝ)) ≤ (r : ℝ) := by
        calc 2 * (c_T * (r : ℝ))
            = (2 * c_T) * (r : ℝ) := by ring
          _ ≤ 1 * (r : ℝ) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
          _ = (r : ℝ) := one_mul _
      linarith
    have hB_up : 1 + (ζ : ℝ) * (q : ℝ) ≤ 1281 * (ζ : ℝ) ^ 2 / α := by
      have hQ0_nonneg : 0 ≤ 640 * (ζ : ℝ) / α := le_trans zero_le_one hQ0_ge1
      have hq_up : (q : ℝ) ≤ 2 * (640 * (ζ : ℝ) / α) := by
        have hc : (q : ℝ) ≤ 640 * (ζ : ℝ) / α + 1 := by
          rw [hq_def]
          exact (Nat.ceil_lt_add_one hQ0_nonneg).le
        linarith
      have h1_le : 1 ≤ (ζ : ℝ) ^ 2 / α := (le_div_iff₀ hα_pos).mpr (by nlinarith)
      have hzq : (ζ : ℝ) * (q : ℝ) ≤ (ζ : ℝ) * (2 * (640 * (ζ : ℝ) / α)) :=
        mul_le_mul_of_nonneg_left hq_up hζ_pos.le
      calc 1 + (ζ : ℝ) * (q : ℝ)
          ≤ (ζ : ℝ) ^ 2 / α + (ζ : ℝ) * (2 * (640 * (ζ : ℝ) / α)) := add_le_add h1_le hzq
        _ = 1281 * (ζ : ℝ) ^ 2 / α := by ring
    have hprod_real : ((T * (1 + ζ * q) : ℕ) : ℝ) ≤ (vg0_card : ℝ) := by
      have hζ2_nonneg : (0 : ℝ) ≤ (ζ : ℝ) ^ 2 := sq_nonneg (ζ : ℝ)
      have hζ2_le_ζ6 : (ζ : ℝ) ^ 2 ≤ (ζ : ℝ) ^ 6 := by
        have h4 : (1 : ℝ) ≤ (ζ : ℝ) ^ 4 := one_le_pow₀ (by linarith)
        calc (ζ : ℝ) ^ 2 = (ζ : ℝ) ^ 2 * 1 := (mul_one _).symm
          _ ≤ (ζ : ℝ) ^ 2 * (ζ : ℝ) ^ 4 := mul_le_mul_of_nonneg_left h4 hζ2_nonneg
          _ = (ζ : ℝ) ^ 6 := by ring
      have hrζ2_nonneg : (0 : ℝ) ≤ (r : ℝ) * (ζ : ℝ) ^ 2 := mul_nonneg (by linarith) hζ2_nonneg
      have hrζ6_nonneg : (0 : ℝ) ≤ (r : ℝ) * (ζ : ℝ) ^ 6 := mul_nonneg (by linarith) hζ6_nonneg
      have hnum : 1281 * (r : ℝ) * (ζ : ℝ) ^ 2 ≤
          (5 / 8 : ℝ) * (C_samp * (r : ℝ) * (ζ : ℝ) ^ 6) := by
        calc 1281 * (r : ℝ) * (ζ : ℝ) ^ 2
            = 1281 * ((r : ℝ) * (ζ : ℝ) ^ 2) := by ring
          _ ≤ 1875 * ((r : ℝ) * (ζ : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right (by norm_num) hrζ2_nonneg
          _ = (1875 * (r : ℝ)) * (ζ : ℝ) ^ 2 := by ring
          _ ≤ (1875 * (r : ℝ)) * (ζ : ℝ) ^ 6 :=
              mul_le_mul_of_nonneg_left hζ2_le_ζ6 (by linarith)
          _ = (5 / 8 : ℝ) * (3000 * ((r : ℝ) * (ζ : ℝ) ^ 6)) := by ring
          _ ≤ (5 / 8 : ℝ) * (C_samp * ((r : ℝ) * (ζ : ℝ) ^ 6)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hCsamp_3000 hrζ6_nonneg) (by norm_num)
          _ = (5 / 8 : ℝ) * (C_samp * (r : ℝ) * (ζ : ℝ) ^ 6) := by ring
      have hB_nonneg : 0 ≤ 1 + (ζ : ℝ) * (q : ℝ) :=
        add_nonneg zero_le_one (mul_nonneg hζ_pos.le (Nat.cast_nonneg q))
      push_cast
      calc (T : ℝ) * (1 + (ζ : ℝ) * (q : ℝ))
          ≤ (r : ℝ) * (1281 * (ζ : ℝ) ^ 2 / α) :=
            mul_le_mul hT_up hB_up hB_nonneg (by linarith)
        _ = 1281 * (r : ℝ) * (ζ : ℝ) ^ 2 / α := by ring
        _ ≤ ((5 / 8 : ℝ) * (C_samp * (r : ℝ) * (ζ : ℝ) ^ 6)) / α :=
            div_le_div_of_nonneg_right hnum hα_pos.le
        _ = (5 / 8 : ℝ) * (C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α) := by ring
        _ ≤ (5 / 8 : ℝ) * (n₀ : ℝ) :=
            mul_le_mul_of_nonneg_left hn₀_lo (by norm_num)
        _ ≤ (vg0_card : ℝ) := hvg0_lo
    exact_mod_cast hprod_real
  exact ⟨hT_ge1, hX_le_T, hT_le_icenter, hq_ge1, hTB_le⟩

/-- Single-tree witness vector properties from `lemma_9_1_TreeCancellation`: support containment,
cardinality bound `≤ 1 + ζ * q`, `‖x‖₂² ≥ 1`, and `‖Sᵀ x‖₂² ≤ α / 4`. -/
private lemma single_tree_witness_bounds {n k ζ q : ℕ} {α : ℝ}
    (S : Matrix (Fin n) (Fin k) ℝ) (V_G0 : Finset (Fin n))
    (iStar : Fin n) (L : Fin k → Finset (Fin n))
    (hα_pos : 0 < α) (hq_ge1 : 1 ≤ q)
    (hq_lo : 640 * (ζ : ℝ) / α ≤ (q : ℝ))
    (hc4 : IsC4FreeRows S V_G0)
    (hi_G0 : iStar ∈ V_G0)
    (hi_norm : vecSqNorm (S iStar) ≤ 160)
    (hi_deg : (rowSupport S iStar).card ≤ ζ)
    (hL_prop : ∀ j ∈ rowSupport S iStar, L j ⊆ V_G0 \ {iStar} ∧ (L j).card = q ∧
      ∀ ℓ ∈ L j, j ∈ rowSupport S ℓ ∧ relWeight S iStar j ≤ relWeight S ℓ j)
    (hL_disj : ∀ j₁ ∈ rowSupport S iStar, ∀ ℓ₁ ∈ L j₁,
      ∀ j₂ ∈ rowSupport S iStar, ∀ ℓ₂ ∈ L j₂,
      (j₁, ℓ₁) ≠ (j₂, ℓ₂) → Disjoint (rowSupport S ℓ₁ \ {j₁}) (rowSupport S ℓ₂ \ {j₂})) :
    let A := insert iStar ((rowSupport S iStar).biUnion L)
    let x := treeCancelVec S iStar q L
    A ⊆ V_G0 ∧
      A.card ≤ 1 + ζ * q ∧
      (∀ i : Fin n, i ∉ A → x i = 0) ∧
      1 ≤ vecSqNorm x ∧
      vecSqNorm (S.transpose.mulVec x) ≤ α / 4 := by
  let A := insert iStar ((rowSupport S iStar).biUnion L)
  let x := treeCancelVec S iStar q L
  have h91 := lemma_9_1_TreeCancellation n k ζ q S V_G0 iStar L
    hq_ge1 hc4 hi_G0 hi_deg hL_prop hL_disj
  have hA_sub : A ⊆ V_G0 := by
    refine Finset.insert_subset hi_G0 ?_
    refine Finset.biUnion_subset.mpr (fun j hj => ?_)
    exact le_trans (hL_prop j hj).1 Finset.sdiff_subset
  have hA_card : A.card ≤ 1 + ζ * q := by
    have hbi : ((rowSupport S iStar).biUnion L).card ≤ ζ * q := by
      calc ((rowSupport S iStar).biUnion L).card
          ≤ ∑ j ∈ rowSupport S iStar, (L j).card := Finset.card_biUnion_le
        _ = ∑ _j ∈ rowSupport S iStar, q :=
            Finset.sum_congr rfl (fun j hj => (hL_prop j hj).2.1)
        _ = (rowSupport S iStar).card * q := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ζ * q := Nat.mul_le_mul_right q hi_deg
    have hins : A.card ≤ ((rowSupport S iStar).biUnion L).card + 1 :=
      Finset.card_insert_le _ _
    omega
  have hx_supp : ∀ i : Fin n, i ∉ A → x i = 0 := by
    intro i hi
    have hi_ne : i ≠ iStar := fun h => hi (h ▸ Finset.mem_insert_self _ _)
    have hi_not_L : ∀ j ∈ rowSupport S iStar, i ∉ L j := by
      intro j hj himem
      exact hi (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨j, hj, himem⟩))
    simp only [x, treeCancelVec, if_neg hi_ne]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [if_neg (hi_not_L j hj)]
  have hx_norm : 1 ≤ vecSqNorm x := by
    have hx_center : x iStar = 1 := by simp [x, treeCancelVec]
    have hterm : (x iStar) ^ 2 ≤ ∑ i : Fin n, (x i) ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ iStar)
    simpa [vecSqNorm, hx_center] using hterm
  have hSx_norm : vecSqNorm (S.transpose.mulVec x) ≤ α / 4 := by
    let y := S.transpose.mulVec x
    have hinner_zero : ∑ c ∈ rowSupport S iStar, (y c) ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun c hc => ?_)
      have hy0 : y c = 0 := h91.1 c hc
      simp [hy0]
    have hsum_eq : vecSqNorm y = ∑ c ∈ (rowSupport S iStar)ᶜ, (y c) ^ 2 := by
      have hsplit := Finset.sum_add_sum_compl (rowSupport S iStar) (fun c => (y c) ^ 2)
      simp only [vecSqNorm]
      linarith
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_ge1
    have hdeg_real : ((rowSupport S iStar).card : ℝ) ≤ (ζ : ℝ) := by exact_mod_cast hi_deg
    have hnorm_nonneg : 0 ≤ vecSqNorm (S iStar) :=
      Finset.sum_nonneg (fun j _ => sq_nonneg (S iStar j))
    have hnum_le : ((rowSupport S iStar).card : ℝ) * vecSqNorm (S iStar) ≤ 160 * (ζ : ℝ) := by
      calc ((rowSupport S iStar).card : ℝ) * vecSqNorm (S iStar)
          ≤ (ζ : ℝ) * 160 :=
            mul_le_mul hdeg_real hi_norm hnorm_nonneg (Nat.cast_nonneg ζ)
        _ = 160 * (ζ : ℝ) := by ring
    have hdiv_le : 160 * (ζ : ℝ) / (q : ℝ) ≤ α / 4 := by
      refine (div_le_iff₀ hq_pos).mpr ?_
      have hα_ne : α ≠ 0 := hα_pos.ne'
      calc 160 * (ζ : ℝ)
          = (α / 4) * (640 * (ζ : ℝ) / α) := by field_simp; ring
        _ ≤ (α / 4) * (q : ℝ) :=
            mul_le_mul_of_nonneg_left hq_lo (by positivity)
    rw [hsum_eq]
    calc ∑ c ∈ (rowSupport S iStar)ᶜ, (y c) ^ 2
        ≤ ((rowSupport S iStar).card : ℝ) * vecSqNorm (S iStar) / (q : ℝ) := h91.2
      _ ≤ 160 * (ζ : ℝ) / (q : ℝ) := div_le_div_of_nonneg_right hnum_le hq_pos.le
      _ ≤ α / 4 := hdiv_le
  exact ⟨hA_sub, hA_card, hx_supp, hx_norm, hSx_norm⟩

/-- **Theorem 9.7 (Existence of a vertex-disjoint witness forest in `G₀`, p. 44).** -/
theorem theorem_9_7_WitnessForest : Theorem_9_7_WitnessForest := by
  rcases lemma_9_4_TuranCenterRows with ⟨C_samp₁, c_T₁, hCs₁, hcT₁, h94⟩
  let c_T : ℝ := min c_T₁ (1 / 16)
  let C_samp₂ : ℝ := max C_samp₁ (max (1 / c_T) 3000)
  have hcT_pos : 0 < c_T := lt_min hcT₁ (by norm_num)
  have hCs₂_pos : 0 < C_samp₂ := lt_of_lt_of_le hCs₁ (le_max_left _ _)
  refine ⟨C_samp₂, c_T, hCs₂_pos, hcT_pos, ?_⟩
  intro K C_samp α n k r ζ n₀ S V_G0 hK hCsamp hα_pos hα_le hr hr_le_k hk_le hζ
    hn₀ hVG0_lo hVG0_hi hc4 hclean
  dsimp only
  let q : ℕ := Nat.ceil (640 * (ζ : ℝ) / α)
  let L : ℕ := q + q * (ζ - 1) ^ 2
  let D : ℕ := ζ * L
  have hCs₁_K : C_samp₁ * K ≤ C_samp := by
    have h1 : C_samp₁ ≤ C_samp₂ := le_max_left _ _
    have hK2 : K ≤ K ^ 2 := by nlinarith
    calc C_samp₁ * K
        ≤ C_samp₂ * K ^ 2 := mul_le_mul h1 hK2 (by linarith) hCs₂_pos.le
      _ ≤ C_samp := hCsamp
  rcases h94 K C_samp α n k r ζ n₀ S V_G0 hK hCs₁_K hα_pos hα_le hr hr_le_k hk_le hζ
    hn₀ hVG0_lo hVG0_hi (fun i hi => (hclean i hi).2.2.2) with
    ⟨k', colOf, V_virt, F, I_center, _hk', hSplit, hI_sub, hI_card, hI_disj⟩
  have hc4_pairs : 2 * V_G0.card ≤ k * (k - 1) :=
    c4Free_card_le_pairs S V_G0 hc4 (fun i hi => (hclean i hi).2.2.1)
  let T : ℕ := Nat.ceil (c_T * (r : ℝ) / (ζ : ℝ) ^ 5)
  have hcT_Cs2 : 1 ≤ c_T * C_samp₂ := by
    have h : 1 / c_T ≤ C_samp₂ := le_trans (le_max_left _ _) (le_max_right _ _)
    have h' := (div_le_iff₀ hcT_pos).mp h
    linarith
  obtain ⟨hT_ge1, hT_lo, hT_le_I, hq_ge1, hTB_le⟩ :=
    witness_forest_param_bounds hcT_pos (min_le_left _ _) (min_le_right _ _)
      hCs₂_pos hcT_Cs2 (le_trans (le_max_right _ _) (le_max_right _ _))
      hK hCsamp hα_pos hα_le hr hk_le hζ hn₀ rfl rfl hVG0_lo hc4_pairs hI_card
  rcases Finset.exists_subset_card_eq hT_le_I with ⟨I_sub, hI_sub_I, hI_sub_card⟩
  let centerEmb := I_sub.orderEmbOfFin hI_sub_card
  let center : Fin T → Fin n := fun s => centerEmb s
  have hcenter_I : ∀ s : Fin T, center s ∈ I_center :=
    fun s => hI_sub_I (Finset.orderEmbOfFin_mem I_sub hI_sub_card s)
  have hcenter_inj : Function.Injective center := centerEmb.injective
  have hcenter_G0 : ∀ s : Fin T, center s ∈ V_G0 :=
    fun s => (Finset.mem_sdiff.mp (hI_sub (hcenter_I s))).1
  have hcenter_not_F : ∀ (s : Fin T) (j' : Fin k'), center s ∉ F j' := by
    intro s j' hmem
    have hnot := (Finset.mem_sdiff.mp (hI_sub (hcenter_I s))).2
    exact hnot (Finset.mem_biUnion.mpr ⟨j', Finset.mem_univ j', hmem⟩)
  rcases hSplit with ⟨hV_sub, hV_col, hV_uniq, _hV_deg, hF_prop⟩
  let virtCol (s : Fin T) (j : Fin k) (hj : j ∈ rowSupport S (center s)) : Fin k' :=
    Classical.choose (hV_uniq (center s) (hcenter_G0 s) j hj)
  have hvirt_spec : ∀ (s : Fin T) (j : Fin k) (hj : j ∈ rowSupport S (center s)),
      colOf (virtCol s j hj) = j ∧ center s ∈ V_virt (virtCol s j hj) :=
    fun s j hj => (Classical.choose_spec (hV_uniq (center s) (hcenter_G0 s) j hj)).1
  have hvirt_card : ∀ (s : Fin T) (j : Fin k) (hj : j ∈ rowSupport S (center s)),
      D ≤ (F (virtCol s j hj)).card ∧
        ∀ ℓ ∈ F (virtCol s j hj), relWeight S (center s) j ≤ relWeight S ℓ j := by
    intro s j hj
    let j' := virtCol s j hj
    have hs_in_V : center s ∈ V_virt j' := (hvirt_spec s j hj).2
    have hs_sdiff : center s ∈ V_virt j' \ F j' :=
      Finset.mem_sdiff.mpr ⟨hs_in_V, hcenter_not_F s j'⟩
    refine ⟨?_, ?_⟩
    · change D ≤ (F j').card
      by_contra hlt
      have hle : (V_virt j').card ≤ D := by
        have hmin : (F j').card = min D (V_virt j').card := (hF_prop j').2.1
        omega
      have heq_card : (V_virt j').card ≤ (F j').card := by
        rw [(hF_prop j').2.1]
        exact le_min hle le_rfl
      have hF_eq : F j' = V_virt j' :=
        Finset.eq_of_subset_of_card_le (hF_prop j').1 heq_card
      exact hcenter_not_F s j' (hF_eq ▸ hs_in_V)
    · intro ℓ hℓ
      have hw := (hF_prop j').2.2 (center s) hs_sdiff ℓ hℓ
      rwa [(hvirt_spec s j hj).1] at hw
  let branchSet : Fin T → Finset (Fin k') := fun s =>
    (rowSupport S (center s)).attach.image (fun j => virtCol s j.1 j.2)
  let J_branch : Finset (Fin k') := Finset.univ.biUnion branchSet
  have hvirt_mem_J : ∀ (s : Fin T) (j : Fin k) (hj : j ∈ rowSupport S (center s)),
      virtCol s j hj ∈ J_branch := by
    intro s j hj
    refine Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_attach _ _, rfl⟩
  have hJ_card : ∀ j' ∈ J_branch, D ≤ (F j').card := by
    intro j' hj'
    rcases Finset.mem_biUnion.mp hj' with ⟨s, _, hs⟩
    rcases Finset.mem_image.mp hs with ⟨⟨j, hj⟩, _, rfl⟩
    exact (hvirt_card s j hj).1
  have hJ_mult : ∀ ℓ : Fin n,
      ((Set.toFinite {j' : Fin k' | j' ∈ J_branch ∧ ℓ ∈ F j'}).toFinset).card ≤ ζ := by
    intro ℓ
    let M_ℓ := (Set.toFinite {j' : Fin k' | j' ∈ J_branch ∧ ℓ ∈ F j'}).toFinset
    change M_ℓ.card ≤ ζ
    rcases M_ℓ.eq_empty_or_nonempty with hempty | ⟨j₀', hj₀'⟩
    · rw [hempty, Finset.card_empty]
      exact Nat.zero_le ζ
    · have hℓ_F₀ : ℓ ∈ F j₀' := ((Set.Finite.mem_toFinset _).mp hj₀').2
      have hℓ_G0 : ℓ ∈ V_G0 := hV_sub j₀' ((hF_prop j₀').1 hℓ_F₀)
      have hinj_col : Set.InjOn colOf (M_ℓ : Set (Fin k')) := by
        intro j₁' hj₁' j₂' hj₂' hcol
        have h₁ : ℓ ∈ V_virt j₁' :=
          (hF_prop j₁').1 (((Set.Finite.mem_toFinset _).mp hj₁').2)
        have h₂ : ℓ ∈ V_virt j₂' :=
          (hF_prop j₂').1 (((Set.Finite.mem_toFinset _).mp hj₂').2)
        have hj_supp : colOf j₁' ∈ rowSupport S ℓ := hV_col j₁' ℓ h₁
        rcases hV_uniq ℓ hℓ_G0 (colOf j₁') hj_supp with ⟨j_u, _, huniq⟩
        exact (huniq j₁' ⟨rfl, h₁⟩).trans (huniq j₂' ⟨hcol.symm, h₂⟩).symm
      have himg_sub : M_ℓ.image colOf ⊆ rowSupport S ℓ := by
        intro j hj
        rcases Finset.mem_image.mp hj with ⟨j', hj', rfl⟩
        exact hV_col j' ℓ ((hF_prop j').1 (((Set.Finite.mem_toFinset _).mp hj').2))
      calc M_ℓ.card
          = (M_ℓ.image colOf).card := (Finset.card_image_of_injOn hinj_col).symm
        _ ≤ (rowSupport S ℓ).card := Finset.card_le_card himg_sub
        _ ≤ ζ := (hclean ℓ hℓ_G0).2.2.2
  rcases lemma_9_6_DisjointLeafReservoirs n k' ζ L D J_branch F
    (by omega) le_rfl hJ_card hJ_mult with ⟨R_res, hR_prop, hR_disj⟩
  let F_cand (s : Fin T) (j : Fin k) : Finset (Fin n) :=
    if hj : j ∈ rowSupport S (center s) then R_res (virtCol s j hj) else ∅
  have hF_cand_eq : ∀ (s : Fin T) (j : Fin k) (hj : j ∈ rowSupport S (center s)),
      F_cand s j = R_res (virtCol s j hj) :=
    fun s j hj => dif_pos hj
  have hleaves_ex : ∀ s : Fin T, ∃ L_s : Fin k → Finset (Fin n),
      (∀ j ∈ rowSupport S (center s), L_s j ⊆ F_cand s j ∧ (L_s j).card = q) ∧
        ∀ j₁ ∈ rowSupport S (center s), ∀ ℓ₁ ∈ L_s j₁,
          ∀ j₂ ∈ rowSupport S (center s), ∀ ℓ₂ ∈ L_s j₂,
            (j₁, ℓ₁) ≠ (j₂, ℓ₂) → Disjoint (rowSupport S ℓ₁ \ {j₁}) (rowSupport S ℓ₂ \ {j₂}) := by
    intro s
    refine lemma_9_2_SingleTreeDisjointLeaves n k ζ q S V_G0 (center s) (F_cand s)
      (by omega) hc4 (fun i hi => (hclean i hi).2.2.2) (hcenter_G0 s) ?_
    intro j hj
    let j' := virtCol s j hj
    have hj'_J : j' ∈ J_branch := hvirt_mem_J s j hj
    rw [hF_cand_eq s j hj]
    have hR_sub_F : R_res j' ⊆ F j' := (hR_prop j' hj'_J).1
    have hR_sub_V : R_res j' ⊆ V_virt j' := le_trans hR_sub_F (hF_prop j').1
    refine ⟨?_, ?_, ?_⟩
    · refine Finset.subset_sdiff.mpr ⟨le_trans hR_sub_V (hV_sub j'), ?_⟩
      rw [Finset.disjoint_singleton_right]
      exact fun hmem => hcenter_not_F s j' (hR_sub_F hmem)
    · intro ℓ hℓ
      have hcol := hV_col j' ℓ (hR_sub_V hℓ)
      rwa [(hvirt_spec s j hj).1] at hcol
    · rw [(hR_prop j' hj'_J).2]
  let leaves (s : Fin T) : Fin k → Finset (Fin n) := Classical.choose (hleaves_ex s)
  have hleaves_spec : ∀ s : Fin T,
      (∀ j ∈ rowSupport S (center s), leaves s j ⊆ F_cand s j ∧ (leaves s j).card = q) ∧
        ∀ j₁ ∈ rowSupport S (center s), ∀ ℓ₁ ∈ leaves s j₁,
          ∀ j₂ ∈ rowSupport S (center s), ∀ ℓ₂ ∈ leaves s j₂,
            (j₁, ℓ₁) ≠ (j₂, ℓ₂) → Disjoint (rowSupport S ℓ₁ \ {j₁}) (rowSupport S ℓ₂ \ {j₂}) :=
    fun s => Classical.choose_spec (hleaves_ex s)
  let A_tree (s : Fin T) : Finset (Fin n) :=
    insert (center s) ((rowSupport S (center s)).biUnion (leaves s))
  let x_tree (s : Fin T) : Fin n → ℝ := treeCancelVec S (center s) q (leaves s)
  have htree_bounds : ∀ s : Fin T,
      A_tree s ⊆ V_G0 ∧
        (A_tree s).card ≤ 1 + ζ * q ∧
        (∀ i : Fin n, i ∉ A_tree s → x_tree s i = 0) ∧
        1 ≤ vecSqNorm (x_tree s) ∧
        vecSqNorm (S.transpose.mulVec (x_tree s)) ≤ α / 4 := by
    intro s
    refine single_tree_witness_bounds S V_G0 (center s) (leaves s)
      hα_pos hq_ge1 (Nat.le_ceil _) hc4 (hcenter_G0 s)
      (hclean (center s) (hcenter_G0 s)).2.1
      (hclean (center s) (hcenter_G0 s)).2.2.2 ?_ (hleaves_spec s).2
    intro j hj
    let j' := virtCol s j hj
    have hj'_J : j' ∈ J_branch := hvirt_mem_J s j hj
    have hL_sub_R : leaves s j ⊆ R_res j' := by
      have h1 := ((hleaves_spec s).1 j hj).1
      rwa [hF_cand_eq s j hj] at h1
    have hR_sub_F : R_res j' ⊆ F j' := (hR_prop j' hj'_J).1
    have hL_sub_F : leaves s j ⊆ F j' := le_trans hL_sub_R hR_sub_F
    have hL_sub_V : leaves s j ⊆ V_virt j' := le_trans hL_sub_F (hF_prop j').1
    refine ⟨?_, ((hleaves_spec s).1 j hj).2, ?_⟩
    · refine Finset.subset_sdiff.mpr ⟨le_trans hL_sub_V (hV_sub j'), ?_⟩
      rw [Finset.disjoint_singleton_right]
      exact fun hmem => hcenter_not_F s j' (hL_sub_F hmem)
    · intro ℓ hℓ
      have hcol := hV_col j' ℓ (hL_sub_V hℓ)
      rw [(hvirt_spec s j hj).1] at hcol
      exact ⟨hcol, (hvirt_card s j hj).2 ℓ (hL_sub_F hℓ)⟩
  have hleaves_in_F : ∀ (s : Fin T) (v : Fin n),
      v ∈ (rowSupport S (center s)).biUnion (leaves s) → ∃ j' : Fin k', v ∈ F j' := by
    intro s v hv
    rcases Finset.mem_biUnion.mp hv with ⟨j, hj, hvL⟩
    let j' := virtCol s j hj
    have h1 := ((hleaves_spec s).1 j hj).1 hvL
    rw [hF_cand_eq s j hj] at h1
    exact ⟨j', (hR_prop j' (hvirt_mem_J s j hj)).1 h1⟩
  have hA_disj : ∀ s u : Fin T, s ≠ u → Disjoint (A_tree s) (A_tree u) := by
    intro s u hne
    rw [Finset.disjoint_left]
    intro v hvs hvu
    rcases Finset.mem_insert.mp hvs with rfl | hvs_L
    · rcases Finset.mem_insert.mp hvu with heq | hvu_L
      · exact hne (hcenter_inj heq)
      · rcases hleaves_in_F u (center s) hvu_L with ⟨j', hj'⟩
        exact hcenter_not_F s j' hj'
    · rcases Finset.mem_insert.mp hvu with rfl | hvu_L
      · rcases hleaves_in_F s (center u) hvs_L with ⟨j', hj'⟩
        exact hcenter_not_F u j' hj'
      · rcases Finset.mem_biUnion.mp hvs_L with ⟨j₁, hj₁, hv₁⟩
        rcases Finset.mem_biUnion.mp hvu_L with ⟨j₂, hj₂, hv₂⟩
        let j₁' := virtCol s j₁ hj₁
        let j₂' := virtCol u j₂ hj₂
        have hv_R₁ : v ∈ R_res j₁' := by
          have h1 := ((hleaves_spec s).1 j₁ hj₁).1 hv₁
          rwa [hF_cand_eq s j₁ hj₁] at h1
        have hv_R₂ : v ∈ R_res j₂' := by
          have h2 := ((hleaves_spec u).1 j₂ hj₂).1 hv₂
          rwa [hF_cand_eq u j₂ hj₂] at h2
        have hj'_ne : j₁' ≠ j₂' := by
          intro heq
          have hs_V : center s ∈ V_virt j₁' := (hvirt_spec s j₁ hj₁).2
          have hu_V : center u ∈ V_virt j₁' := heq ▸ (hvirt_spec u j₂ hj₂).2
          exact hI_disj (center s) (hcenter_I s) (center u) (hcenter_I u)
            (fun hc => hne (hcenter_inj hc)) j₁' ⟨hs_V, hu_V⟩
        exact Finset.disjoint_left.mp
          (hR_disj j₁' (hvirt_mem_J s j₁ hj₁) j₂' (hvirt_mem_J u j₂ hj₂) hj'_ne)
          hv_R₁ hv_R₂
  rcases pad_disjoint_subsets V_G0 T (1 + ζ * q) A_tree
    (fun s => (htree_bounds s).1) (fun s => (htree_bounds s).2.1) hA_disj hTB_le with
    ⟨V_tree, hV_prop, hV_disj⟩
  refine ⟨T, V_tree, x_tree, hT_ge1, hT_lo, ?_, hV_disj, ?_⟩
  · exact fun s => ⟨(hV_prop s).2.1, (hV_prop s).2.2⟩
  · intro s
    refine ⟨?_, (htree_bounds s).2.2.2.1, (htree_bounds s).2.2.2.2⟩
    intro i hi
    exact (htree_bounds s).2.2.1 i (fun hA => hi ((hV_prop s).1 hA))

end Osi.LowerBound
