import Osi.Spec

/-!
# Section 9.3: Turán / Caro–Wei and Virtual-Column Center Extraction

Proves `Lemma_9_3_TuranCaroWei` and `Lemma_9_4_TuranCenterRows`.
-/

namespace Osi.LowerBound

open Osi.Spec

/-! ### Section 9.3.1: Caro–Wei and Turán independent-set lower bound (Lemma 9.3) -/

private def degOn {V : Type*} (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (v : V) : ℕ :=
  (S.filter (H.Adj v)).card

private lemma degOn_mono {V : Type*} (H : SimpleGraph V) [DecidableRel H.Adj]
    {S' S : Finset V} (hsub : S' ⊆ S) (v : V) :
    degOn H S' v ≤ degOn H S v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hsub)

private lemma caro_wei_aux {V : Type*} [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∀ (c : ℕ) (S : Finset V), S.card = c →
      ∃ I ⊆ S, (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ H.Adj u v) ∧
        (∑ v ∈ S, (1 : ℝ) / (1 + (degOn H S v : ℝ))) ≤ (I.card : ℝ) := by
  intro c
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro S hSc
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    · obtain ⟨v₀, hv₀S, hmin⟩ := S.exists_min_image (degOn H S) hS
      let N : Finset V := insert v₀ (S.filter (H.Adj v₀))
      have hNsub : N ⊆ S :=
        Finset.insert_subset_iff.mpr ⟨hv₀S, Finset.filter_subset _ _⟩
      have hv₀N_not : v₀ ∉ S.filter (H.Adj v₀) := by
        simp
      have hNcard : N.card = 1 + degOn H S v₀ := by
        rw [Finset.card_insert_of_notMem hv₀N_not, add_comm]
        rfl
      let S' : Finset V := S \ N
      have hS'sub : S' ⊆ S := Finset.sdiff_subset
      have hS'lt : S'.card < c := by
        rw [← hSc]
        refine Finset.card_lt_card ⟨hS'sub, fun h => ?_⟩
        have : v₀ ∈ S' := h hv₀S
        exact (Finset.mem_sdiff.mp this).2 (Finset.mem_insert_self _ _)
      obtain ⟨I', hI'sub, hI'ind, hI'sum⟩ := ih S'.card hS'lt S' rfl
      have hv₀I' : v₀ ∉ I' := fun h =>
        (Finset.mem_sdiff.mp (hI'sub h)).2 (Finset.mem_insert_self _ _)
      refine ⟨insert v₀ I', Finset.insert_subset_iff.mpr ⟨hv₀S, hI'sub.trans hS'sub⟩, ?_, ?_⟩
      · intro u hu v hv huv
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · rcases Finset.mem_insert.mp hv with rfl | hv'
          · exact absurd rfl huv
          · have hvS' := Finset.mem_sdiff.mp (hI'sub hv')
            intro hadj
            exact hvS'.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hvS'.1, hadj⟩))
        · rcases Finset.mem_insert.mp hv with rfl | hv'
          · have huS' := Finset.mem_sdiff.mp (hI'sub hu')
            intro hadj
            exact huS'.2 (Finset.mem_insert_of_mem
              (Finset.mem_filter.mpr ⟨huS'.1, hadj.symm⟩))
          · exact hI'ind u hu' v hv' huv
      · have hsplit := Finset.sum_sdiff hNsub (f := fun v => (1 : ℝ) / (1 + (degOn H S v : ℝ)))
        have hsumS' : (∑ v ∈ S', (1 : ℝ) / (1 + (degOn H S v : ℝ))) ≤ (I'.card : ℝ) := by
          refine le_trans ?_ hI'sum
          refine Finset.sum_le_sum fun u _ => ?_
          have hdeg : (degOn H S' u : ℝ) ≤ (degOn H S u : ℝ) := by
            exact_mod_cast degOn_mono H hS'sub u
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
        have hsumN : (∑ v ∈ N, (1 : ℝ) / (1 + (degOn H S v : ℝ))) ≤ 1 := by
          calc
            (∑ v ∈ N, (1 : ℝ) / (1 + (degOn H S v : ℝ)))
                ≤ ∑ _v ∈ N, (1 : ℝ) / (1 + (degOn H S v₀ : ℝ)) := by
                  refine Finset.sum_le_sum fun u hu => ?_
                  have hdeg : (degOn H S v₀ : ℝ) ≤ (degOn H S u : ℝ) := by
                    exact_mod_cast hmin u (hNsub hu)
                  exact one_div_le_one_div_of_le (by positivity) (by linarith)
            _ = (N.card : ℝ) * ((1 : ℝ) / (1 + (degOn H S v₀ : ℝ))) := by
                  simp
            _ = 1 := by
                  have hpos : (0 : ℝ) < 1 + (degOn H S v₀ : ℝ) := by positivity
                  rw [hNcard, Nat.cast_add, Nat.cast_one]
                  field_simp
        rw [Finset.card_insert_of_notMem hv₀I', Nat.cast_add, Nat.cast_one, ← hsplit]
        linarith

/-- **Lemma 9.3 (Turán / Caro–Wei independent-set lower bound, p. 42).** -/
theorem lemma_9_3_TuranCaroWei : Lemma_9_3_TuranCaroWei := by
  intro m H hm
  classical
  dsimp only
  obtain ⟨I, _, hIind, hIsum⟩ := caro_wei_aux H (Finset.univ : Finset (Fin m)).card Finset.univ rfl
  refine ⟨I, hIind, ?_⟩
  have hdeg_eq : ∀ v : Fin m, degOn H Finset.univ v = H.degree v := by
    intro v
    simp [degOn, ← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_def]
  have hedge_eq : ((Set.toFinite H.edgeSet).toFinset).card = H.edgeFinset.card := by
    congr 1
    ext e
    simp
  have hsum_deg : (∑ v : Fin m, (H.degree v : ℝ)) =
      2 * (((Set.toFinite H.edgeSet).toFinset).card : ℝ) := by
    have hnat : ∑ v : Fin m, H.degree v = 2 * ((Set.toFinite H.edgeSet).toFinset).card := by
      rw [hedge_eq]
      exact H.sum_degrees_eq_twice_card_edges
    exact_mod_cast hnat
  have hcs := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin m))
    (fun _ => (1 : ℝ)) (g := fun v => 1 + (H.degree v : ℝ)) (fun _ _ => by positivity)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdenom : (∑ v : Fin m, (1 + (H.degree v : ℝ))) =
      (m : ℝ) * (1 + 2 * (((Set.toFinite H.edgeSet).toFinset).card : ℝ) / (m : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, hsum_deg]
    field_simp
  have hlhs : ((∑ _v : Fin m, (1 : ℝ)) ^ 2) / (∑ v : Fin m, (1 + (H.degree v : ℝ))) =
      (m : ℝ) / (1 + 2 * (((Set.toFinite H.edgeSet).toFinset).card : ℝ) / (m : ℝ)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hdenom]
    have hd_pos : (0 : ℝ) < 1 + 2 * (((Set.toFinite H.edgeSet).toFinset).card : ℝ) / (m : ℝ) := by
      positivity
    field_simp
  have hrhs : (∑ v : Fin m, (1 : ℝ) ^ 2 / (1 + (H.degree v : ℝ))) =
      ∑ v : Fin m, (1 : ℝ) / (1 + (degOn H Finset.univ v : ℝ)) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [one_pow, hdeg_eq v]
  linarith

/-! ### Section 9.3.2: Virtual-column splitting and top-`D` selection -/

private lemma exists_top_finset {α : Type*} [DecidableEq α] (w : α → ℝ) :
    ∀ (D : ℕ) (S : Finset α),
      ∃ F ⊆ S, F.card = min D S.card ∧ ∀ i ∈ S \ F, ∀ ℓ ∈ F, w i ≤ w ℓ := by
  intro D
  induction D with
  | zero =>
    intro S
    exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ D ih =>
    intro S
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    · obtain ⟨m, hmS, hmax⟩ := S.exists_max_image w hS
      obtain ⟨F', hF'sub, hF'card, hF'ord⟩ := ih (S.erase m)
      have hmF' : m ∉ F' := fun h => (Finset.mem_erase.mp (hF'sub h)).1 rfl
      refine ⟨insert m F',
        Finset.insert_subset_iff.mpr ⟨hmS, hF'sub.trans (Finset.erase_subset m S)⟩, ?_, ?_⟩
      · have hScard_pos : 0 < S.card := Finset.card_pos.mpr hS
        rw [Finset.card_insert_of_notMem hmF', hF'card, Finset.card_erase_of_mem hmS]
        omega
      · intro i hi ℓ hℓ
        rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hi
        rcases Finset.mem_insert.mp hℓ with rfl | hℓF'
        · exact hmax i hi.1
        · exact hF'ord i (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hi.2.1, hi.1⟩, hi.2.2⟩) ℓ hℓF'

private noncomputable def chunkFinset {n : ℕ} (A : Finset (Fin n)) (Δ t : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun x : Fin A.card => x.1 / Δ = t)).map (A.orderEmbOfFin rfl).toEmbedding

private lemma chunkFinset_subset {n : ℕ} (A : Finset (Fin n)) (Δ t : ℕ) :
    chunkFinset A Δ t ⊆ A := by
  intro i hi
  rcases Finset.mem_map.mp hi with ⟨x, _, rfl⟩
  exact A.orderEmbOfFin_mem rfl x

private lemma chunkFinset_card_le {n : ℕ} (A : Finset (Fin n)) {Δ : ℕ} (hΔ : 1 ≤ Δ) (t : ℕ) :
    (chunkFinset A Δ t).card ≤ Δ := by
  rw [chunkFinset, Finset.card_map]
  have hle := Finset.card_le_card_of_injOn
    (fun x : Fin A.card => (⟨x.1 % Δ, Nat.mod_lt x.1 hΔ⟩ : Fin Δ))
    (s := Finset.univ.filter (fun x : Fin A.card => x.1 / Δ = t))
    (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
    (fun x hx y hy hxy => by
      have hxdiv : x.1 / Δ = t := (Finset.mem_filter.mp hx).2
      have hydiv : y.1 / Δ = t := (Finset.mem_filter.mp hy).2
      have hmod : x.1 % Δ = y.1 % Δ := congrArg Fin.val hxy
      apply Fin.ext
      rw [← Nat.div_add_mod x.1 Δ, ← Nat.div_add_mod y.1 Δ, hxdiv, hydiv, hmod])
  simpa using hle

private lemma div_lt_ceil_div {x m Δ : ℕ} (hx : x < m) (hΔ : 1 ≤ Δ) :
    x / Δ < (m + Δ - 1) / Δ := by
  have h1 : (x / Δ) * Δ ≤ x := Nat.div_mul_le_self x Δ
  have h2 : (x / Δ + 1) * Δ ≤ m + Δ - 1 := by
    rw [Nat.add_one_mul]
    omega
  exact (Nat.le_div_iff_mul_le hΔ).mpr h2

private lemma existsUnique_mem_chunkFinset {n : ℕ} (A : Finset (Fin n)) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    {i : Fin n} (hi : i ∈ A) :
    ∃! t : Fin ((A.card + Δ - 1) / Δ), i ∈ chunkFinset A Δ t.1 := by
  have hi' : i ∈ Finset.map (A.orderEmbOfFin rfl).toEmbedding Finset.univ := by
    rwa [A.map_orderEmbOfFin_univ rfl]
  rcases Finset.mem_map.mp hi' with ⟨x₀, _, hx₀⟩
  refine ⟨⟨x₀.1 / Δ, div_lt_ceil_div x₀.2 hΔ⟩, ?_, ?_⟩
  · exact Finset.mem_map.mpr ⟨x₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, hx₀⟩
  · intro t ht
    rcases Finset.mem_map.mp ht with ⟨x, hx, hxi⟩
    have hxx₀ : x = x₀ := (A.orderEmbOfFin rfl).injective (hxi.trans hx₀.symm)
    subst hxx₀
    ext
    exact (Finset.mem_filter.mp hx).2.symm

private lemma pred_ceil_div_mul_le (m : ℕ) {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    (((m + Δ - 1) / Δ) - 1) * Δ ≤ m := by
  set c := (m + Δ - 1) / Δ
  rcases le_or_gt c 1 with hc | hc
  · have hc0 : c - 1 = 0 := by omega
    simp [hc0]
  · have hmul : c * Δ ≤ m + Δ - 1 := Nat.div_mul_le_self (m + Δ - 1) Δ
    have hsplit : (c - 1) * Δ + Δ = c * Δ := by
      rw [← Nat.add_one_mul]
      congr 1
      omega
    omega

private lemma exists_virtual_column_splitting {n k ζ n₀ Δ D : ℕ}
    (S : Matrix (Fin n) (Fin k) ℝ) (V_G0 : Finset (Fin n))
    (hΔ : 1 ≤ Δ) (hVG0_hi : V_G0.card ≤ n₀)
    (hsparse : ∀ i ∈ V_G0, (rowSupport S i).card ≤ ζ)
    (hζn₀ : ζ * n₀ ≤ k * Δ) :
    ∃ (k' : ℕ) (colOf : Fin k' → Fin k) (V_virt F : Fin k' → Finset (Fin n)),
      k' ≤ 2 * k ∧ IsVirtualColumnSplitting S V_G0 Δ D colOf V_virt F := by
  let Inc : Fin k → Finset (Fin n) := fun j => V_G0.filter (fun i => j ∈ rowSupport S i)
  let c : Fin k → ℕ := fun j => ((Inc j).card + Δ - 1) / Δ
  let VirtIdx := Σ j : Fin k, Fin (c j)
  let k' : ℕ := Fintype.card VirtIdx
  let eVirt : VirtIdx ≃ Fin k' := Fintype.equivFin VirtIdx
  let colOf : Fin k' → Fin k := fun j' => (eVirt.symm j').1
  let V_virt : Fin k' → Finset (Fin n) :=
    fun j' => chunkFinset (Inc (eVirt.symm j').1) Δ (eVirt.symm j').2.1
  choose F hF using fun j' : Fin k' =>
    exists_top_finset (fun i => relWeight S i (colOf j')) D (V_virt j')
  have hk'_eq : k' = ∑ j : Fin k, c j := by
    simp [k', VirtIdx]
  have hsum_inc : (∑ j : Fin k, (Inc j).card) ≤ ζ * n₀ := by
    have hswap : (∑ j : Fin k, (Inc j).card) = ∑ i ∈ V_G0, (rowSupport S i).card := by
      simp_rw [Inc, Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.card_filter]
      congr 1
      ext j
      simp
    calc
      (∑ j : Fin k, (Inc j).card) = ∑ i ∈ V_G0, (rowSupport S i).card := hswap
      _ ≤ ∑ _i ∈ V_G0, ζ := Finset.sum_le_sum fun i hi => hsparse i hi
      _ = V_G0.card * ζ := by simp
      _ ≤ n₀ * ζ := Nat.mul_le_mul_right ζ hVG0_hi
      _ = ζ * n₀ := Nat.mul_comm n₀ ζ
  have hk'_le : k' ≤ 2 * k := by
    have hsum_pred_mul : (∑ j : Fin k, (c j - 1)) * Δ ≤ k * Δ := by
      calc
        (∑ j : Fin k, (c j - 1)) * Δ = ∑ j : Fin k, (c j - 1) * Δ := Finset.sum_mul _ _ _
        _ ≤ ∑ j : Fin k, (Inc j).card :=
          Finset.sum_le_sum fun j _ => pred_ceil_div_mul_le (Inc j).card hΔ
        _ ≤ ζ * n₀ := hsum_inc
        _ ≤ k * Δ := hζn₀
    have hsum_pred : (∑ j : Fin k, (c j - 1)) ≤ k :=
      Nat.le_of_mul_le_mul_right hsum_pred_mul hΔ
    calc
      k' = ∑ j : Fin k, c j := hk'_eq
      _ ≤ ∑ j : Fin k, (1 + (c j - 1)) := Finset.sum_le_sum fun j _ => by omega
      _ = k + ∑ j : Fin k, (c j - 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          mul_one]
      _ ≤ k + k := Nat.add_le_add_left hsum_pred k
      _ = 2 * k := ( two_mul k ).symm
  refine ⟨k', colOf, V_virt, F, hk'_le, ?_, ?_, ?_, ?_, ?_⟩
  · intro j'
    exact (chunkFinset_subset _ _ _).trans (Finset.filter_subset _ _)
  · intro j' i hi
    have hi_inc : i ∈ Inc (colOf j') := chunkFinset_subset _ _ _ hi
    exact (Finset.mem_filter.mp hi_inc).2
  · intro i hi j hj
    have hi_inc : i ∈ Inc j := Finset.mem_filter.mpr ⟨hi, hj⟩
    obtain ⟨t, ht, huniq⟩ := existsUnique_mem_chunkFinset (Inc j) hΔ hi_inc
    let p : VirtIdx := ⟨j, t⟩
    refine ⟨eVirt p, ?_, ?_⟩
    · dsimp only [colOf, V_virt]
      rw [eVirt.symm_apply_apply p]
      exact ⟨rfl, ht⟩
    · rintro j' ⟨hcol, hmem⟩
      obtain ⟨⟨j₂, t₂⟩, rfl⟩ : ∃ q : VirtIdx, eVirt q = j' :=
        ⟨eVirt.symm j', eVirt.apply_symm_apply j'⟩
      have hsymm : eVirt.symm (eVirt ⟨j₂, t₂⟩) = ⟨j₂, t₂⟩ :=
        eVirt.symm_apply_apply ⟨j₂, t₂⟩
      have hj₂ : j₂ = j := by
        dsimp only [colOf] at hcol
        rw [hsymm] at hcol
        exact hcol
      subst j₂
      have ht₂ : i ∈ chunkFinset (Inc j) Δ t₂.1 := by
        dsimp only [V_virt] at hmem
        rw [hsymm] at hmem
        exact hmem
      have htt₂ : t₂ = t := huniq t₂ ht₂
      subst t₂
      rfl
  · intro j'
    exact chunkFinset_card_le _ hΔ _
  · exact hF

/-! ### Section 9.3.3: Conflict graph degree bound and center-row extraction (Lemma 9.4) -/

private def conflictGraph {n k' : ℕ} (V_virt : Fin k' → Finset (Fin n))
    (J_elig : Finset (Fin n)) : SimpleGraph (Fin J_elig.card) where
  Adj a b := a ≠ b ∧
    ∃ j' : Fin k', J_elig.orderEmbOfFin rfl a ∈ V_virt j' ∧
      J_elig.orderEmbOfFin rfl b ∈ V_virt j'
  symm := ⟨fun _ _ ⟨hab, j', ha, hb⟩ => ⟨hab.symm, j', hb, ha⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

private lemma conflictGraph_degree_le {n k k' ζ Δ D : ℕ}
    (S : Matrix (Fin n) (Fin k) ℝ) (V_G0 : Finset (Fin n))
    (colOf : Fin k' → Fin k) (V_virt F : Fin k' → Finset (Fin n))
    (hsplit : IsVirtualColumnSplitting S V_G0 Δ D colOf V_virt F)
    (hsparse : ∀ i ∈ V_G0, (rowSupport S i).card ≤ ζ)
    {J_elig : Finset (Fin n)} (hJsub : J_elig ⊆ V_G0)
    [DecidableRel (conflictGraph V_virt J_elig).Adj]
    (a : Fin J_elig.card) :
    (conflictGraph V_virt J_elig).degree a ≤ ζ * Δ := by
  rcases hsplit with ⟨_, hcol_supp, huniq_virt, hcard_le, _⟩
  let u : Fin n := J_elig.orderEmbOfFin rfl a
  have huV : u ∈ V_G0 := hJsub (J_elig.orderEmbOfFin_mem rfl a)
  let VirtOf : Finset (Fin k') := Finset.univ.filter (fun j' : Fin k' => u ∈ V_virt j')
  have hVirtOf_card : VirtOf.card ≤ ζ := by
    have hinj : VirtOf.card ≤ (rowSupport S u).card :=
      Finset.card_le_card_of_injOn colOf
        (fun j' hj' =>
          Finset.mem_coe.mpr (hcol_supp j' u (Finset.mem_filter.mp (Finset.mem_coe.mp hj')).2))
        (fun j₁' hj₁' j₂' hj₂' hcol_eq => by
          have hu₁ : u ∈ V_virt j₁' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj₁')).2
          have hu₂ : u ∈ V_virt j₂' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj₂')).2
          have hj_supp : colOf j₁' ∈ rowSupport S u := hcol_supp j₁' u hu₁
          obtain ⟨_, _, huniq⟩ := huniq_virt u huV (colOf j₁') hj_supp
          have h1 : j₁' = _ := huniq j₁' ⟨rfl, hu₁⟩
          have h2 : j₂' = _ := huniq j₂' ⟨hcol_eq.symm, hu₂⟩
          exact h1.trans h2.symm)
    exact hinj.trans (hsparse u huV)
  have hdeg_le_biUnion :
      (conflictGraph V_virt J_elig).degree a ≤ (VirtOf.biUnion V_virt).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_card_of_injOn (fun b => J_elig.orderEmbOfFin rfl b)
      (fun b hb => by
        rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hb
        rcases hb.2 with ⟨j', hua, hub⟩
        exact Finset.mem_coe.mpr
          (Finset.mem_biUnion.mpr ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hua⟩, hub⟩))
      (fun b₁ _ b₂ _ h => (J_elig.orderEmbOfFin rfl).injective h)
  calc
    (conflictGraph V_virt J_elig).degree a
        ≤ (VirtOf.biUnion V_virt).card := hdeg_le_biUnion
    _ ≤ ∑ j' ∈ VirtOf, (V_virt j').card := Finset.card_biUnion_le
    _ ≤ ∑ _j' ∈ VirtOf, Δ := Finset.sum_le_sum fun j' _ => hcard_le j'
    _ = VirtOf.card * Δ := by simp
    _ ≤ ζ * Δ := Nat.mul_le_mul_right Δ hVirtOf_card

private lemma conflict_indep_extraction {n k k' ζ Δ D : ℕ}
    (S : Matrix (Fin n) (Fin k) ℝ) (V_G0 : Finset (Fin n))
    (colOf : Fin k' → Fin k) (V_virt F : Fin k' → Finset (Fin n))
    (hsplit : IsVirtualColumnSplitting S V_G0 Δ D colOf V_virt F)
    (hsparse : ∀ i ∈ V_G0, (rowSupport S i).card ≤ ζ)
    {J_elig : Finset (Fin n)} (hJsub : J_elig ⊆ V_G0) (hm : 1 ≤ J_elig.card) :
    ∃ I_center : Finset (Fin n),
      I_center ⊆ J_elig ∧
        (J_elig.card : ℝ) / (1 + (ζ : ℝ) * (Δ : ℝ)) ≤ (I_center.card : ℝ) ∧
        ∀ u ∈ I_center, ∀ v ∈ I_center, u ≠ v →
          ∀ j' : Fin k', ¬ (u ∈ V_virt j' ∧ v ∈ V_virt j') := by
  classical
  let H := conflictGraph V_virt J_elig
  obtain ⟨I, hIind, hIcard⟩ := lemma_9_3_TuranCaroWei J_elig.card H hm
  let I_center : Finset (Fin n) := I.map (J_elig.orderEmbOfFin rfl).toEmbedding
  have hIc_sub : I_center ⊆ J_elig := by
    intro u hu
    rcases Finset.mem_map.mp hu with ⟨a, _, rfl⟩
    exact J_elig.orderEmbOfFin_mem rfl a
  have hedge_eq : ((Set.toFinite H.edgeSet).toFinset).card = H.edgeFinset.card := by
    congr 1
    ext e
    simp
  have h2e_nat : 2 * ((Set.toFinite H.edgeSet).toFinset).card ≤ J_elig.card * (ζ * Δ) := by
    rw [hedge_eq, ← H.sum_degrees_eq_twice_card_edges]
    calc
      (∑ a : Fin J_elig.card, H.degree a)
          ≤ ∑ _a : Fin J_elig.card, (ζ * Δ) :=
            Finset.sum_le_sum fun a _ =>
              conflictGraph_degree_le S V_G0 colOf V_virt F hsplit hsparse hJsub a
      _ = J_elig.card * (ζ * Δ) := by simp
  have hm_pos : (0 : ℝ) < (J_elig.card : ℝ) := by exact_mod_cast hm
  have hd_avg_le :
      2 * (((Set.toFinite H.edgeSet).toFinset).card : ℝ) / (J_elig.card : ℝ) ≤
        (ζ : ℝ) * (Δ : ℝ) := by
    rw [div_le_iff₀ hm_pos]
    have hcast : (2 : ℝ) * (((Set.toFinite H.edgeSet).toFinset).card : ℝ) ≤
        (J_elig.card : ℝ) * ((ζ : ℝ) * (Δ : ℝ)) := by exact_mod_cast h2e_nat
    linarith
  have hd_pos :
      (0 : ℝ) < 1 + 2 * (((Set.toFinite H.edgeSet).toFinset).card : ℝ) / (J_elig.card : ℝ) := by
    positivity
  have hcard_bound :
      (J_elig.card : ℝ) / (1 + (ζ : ℝ) * (Δ : ℝ)) ≤ (I_center.card : ℝ) := by
    have hIc_eq : I_center.card = I.card := Finset.card_map _
    rw [hIc_eq]
    refine le_trans ?_ hIcard
    exact div_le_div_of_nonneg_left (by positivity) hd_pos (by linarith)
  refine ⟨I_center, hIc_sub, hcard_bound, ?_⟩
  intro u hu v hv huv j' ⟨hu_mem, hv_mem⟩
  rcases Finset.mem_map.mp hu with ⟨a, haI, rfl⟩
  rcases Finset.mem_map.mp hv with ⟨b, hbI, rfl⟩
  have hab : a ≠ b := fun h => huv (congrArg _ h)
  exact hIind a haI b hbI hab ⟨hab, j', hu_mem, hv_mem⟩

/-- **Lemma 9.4 (Virtual column splitting and Turán extraction of center rows, p. 42).** -/
theorem lemma_9_4_TuranCenterRows : Lemma_9_4_TuranCenterRows := by
  refine ⟨10000, 1 / 10, by norm_num, by norm_num, ?_⟩
  intro K C_samp α n k r ζ n₀ S V_G0 hK hCsamp hα0 hα1 hr hrk hkKr hζ hn₀ hVG0_lo hVG0_hi hsparse
  dsimp only
  set Δ : ℕ := Nat.ceil ((ζ : ℝ) * (n₀ : ℝ) / (k : ℝ))
  set q : ℕ := Nat.ceil (640 * (ζ : ℝ) / α)
  set L : ℕ := q + q * (ζ - 1) ^ 2
  set D : ℕ := ζ * L
  have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have : 2 ≤ k := le_trans hr hrk
    positivity
  have hζ_ge2 : (2 : ℝ) ≤ (ζ : ℝ) := by exact_mod_cast hζ
  have hζ_pos : (0 : ℝ) < (ζ : ℝ) := by linarith
  have hCsamp_pos : 0 < C_samp := by linarith
  have hn₀_ge : 10000 * K * (r : ℝ) * (ζ : ℝ) ^ 6 / α ≤ (n₀ : ℝ) := by
    have h1 : 10000 * K * (r : ℝ) * (ζ : ℝ) ^ 6 / α ≤ C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α := by
      gcongr
    have h2 : C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α ≤ (n₀ : ℝ) := by
      rw [hn₀]
      exact Nat.le_ceil _
    exact h1.trans h2
  have hn₀_ge2 : (2 : ℝ) ≤ (n₀ : ℝ) := by
    have hζ6_ge1 : (1 : ℝ) ≤ (ζ : ℝ) ^ 6 := one_le_pow₀ (by linarith)
    have hr_ge2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hnum : 2 * α ≤ 10000 * K * (r : ℝ) * (ζ : ℝ) ^ 6 := by
      have : (2 : ℝ) ≤ 10000 * (K * (r : ℝ)) * (ζ : ℝ) ^ 6 := by nlinarith
      nlinarith
    have hdiv : (2 : ℝ) ≤ 10000 * K * (r : ℝ) * (ζ : ℝ) ^ 6 / α :=
      (le_div_iff₀ hα0).mpr hnum
    exact hdiv.trans hn₀_ge
  have hratio_ge1 : (1 : ℝ) ≤ (ζ : ℝ) * (n₀ : ℝ) / (k : ℝ) := by
    rw [one_le_div hk_pos]
    have hζ6_ge1 : (1 : ℝ) ≤ (ζ : ℝ) ^ 6 := one_le_pow₀ (by linarith)
    have hKr_le_n₀ : K * (r : ℝ) ≤ (n₀ : ℝ) := by
      have hnum : K * (r : ℝ) * α ≤ 10000 * K * (r : ℝ) * (ζ : ℝ) ^ 6 := by
        have hKr_pos : 0 ≤ K * (r : ℝ) := by positivity
        nlinarith
      exact ((le_div_iff₀ hα0).mpr hnum).trans hn₀_ge
    nlinarith
  have hΔ_pos : 1 ≤ Δ := by
    have : 0 < (ζ : ℝ) * (n₀ : ℝ) / (k : ℝ) := by linarith
    exact Nat.ceil_pos.mpr this
  have hζn₀_le : ζ * n₀ ≤ k * Δ := by
    have hceil : (ζ : ℝ) * (n₀ : ℝ) / (k : ℝ) ≤ (Δ : ℝ) := Nat.le_ceil _
    have hreal : (ζ : ℝ) * (n₀ : ℝ) ≤ (k : ℝ) * (Δ : ℝ) := by
      have := (div_le_iff₀ hk_pos).mp hceil
      linarith
    exact_mod_cast hreal
  obtain ⟨k', colOf, V_virt, F, hk'_le, hsplit⟩ :=
    exists_virtual_column_splitting (D := D) S V_G0 hΔ_pos hVG0_hi hsparse hζn₀_le
  let J_elig : Finset (Fin n) := V_G0 \ Finset.univ.biUnion F
  have hF_biUnion_le : (Finset.univ.biUnion F).card ≤ (2 * k) * D := by
    calc
      (Finset.univ.biUnion F).card
          ≤ ∑ j' : Fin k', (F j').card := Finset.card_biUnion_le
      _ ≤ ∑ _j' : Fin k', D := by
            refine Finset.sum_le_sum fun j' _ => ?_
            rw [(hsplit.2.2.2.2 j').2.1]
            exact Nat.min_le_left _ _
      _ = k' * D := by simp
      _ ≤ (2 * k) * D := Nat.mul_le_mul_right D hk'_le
  have hD_le : (D : ℝ) ≤ 641 * (ζ : ℝ) ^ 4 / α := by
    have hL_nat : L ≤ q * ζ ^ 2 := by
      have h1 : 1 + (ζ - 1) ^ 2 ≤ ζ ^ 2 := by
        have hζ1 : (ζ - 1) + 1 = ζ := by omega
        calc
          1 + (ζ - 1) ^ 2 ≤ (ζ - 1) ^ 2 + 2 * (ζ - 1) + 1 := by omega
          _ = ((ζ - 1) + 1) ^ 2 := by ring
          _ = ζ ^ 2 := by rw [hζ1]
      calc
        L = q * (1 + (ζ - 1) ^ 2) := by ring
        _ ≤ q * ζ ^ 2 := Nat.mul_le_mul_left q h1
    have hD_nat : D ≤ q * ζ ^ 3 := by
      calc
        D = ζ * L := rfl
        _ ≤ ζ * (q * ζ ^ 2) := Nat.mul_le_mul_left ζ hL_nat
        _ = q * ζ ^ 3 := by ring
    have hD_cast : (D : ℝ) ≤ (q : ℝ) * (ζ : ℝ) ^ 3 := by exact_mod_cast hD_nat
    have hq_le : (q : ℝ) ≤ 641 * (ζ : ℝ) / α := by
      have hceil : (q : ℝ) ≤ 640 * (ζ : ℝ) / α + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      have hone : (1 : ℝ) ≤ (ζ : ℝ) / α := (one_le_div hα0).mpr (by linarith)
      calc
        (q : ℝ) ≤ 640 * (ζ : ℝ) / α + (ζ : ℝ) / α := by linarith
        _ = 641 * (ζ : ℝ) / α := by ring
    calc
      (D : ℝ) ≤ (q : ℝ) * (ζ : ℝ) ^ 3 := hD_cast
      _ ≤ (641 * (ζ : ℝ) / α) * (ζ : ℝ) ^ 3 := by gcongr
      _ = 641 * (ζ : ℝ) ^ 4 / α := by ring
  have h2kD_le : 2 * (k : ℝ) * (D : ℝ) ≤ (n₀ : ℝ) / 8 := by
    have hζ2_ge4 : (4 : ℝ) ≤ (ζ : ℝ) ^ 2 := by nlinarith
    have hζ4_le : 4 * (ζ : ℝ) ^ 4 ≤ (ζ : ℝ) ^ 6 := by
      have hpos4 : (0 : ℝ) ≤ (ζ : ℝ) ^ 4 := by positivity
      calc
        4 * (ζ : ℝ) ^ 4 ≤ (ζ : ℝ) ^ 2 * (ζ : ℝ) ^ 4 := by nlinarith
        _ = (ζ : ℝ) ^ 6 := by ring
    calc
      2 * (k : ℝ) * (D : ℝ)
          ≤ 2 * (K * (r : ℝ)) * (641 * (ζ : ℝ) ^ 4 / α) := by gcongr
      _ = 1282 * (K * (r : ℝ) * (ζ : ℝ) ^ 4 / α) := by ring
      _ ≤ 5000 * (K * (r : ℝ) * (ζ : ℝ) ^ 4 / α) := by
            have hKr_nonneg : 0 ≤ K * (r : ℝ) * (ζ : ℝ) ^ 4 / α := by positivity
            linarith
      _ = 1250 * K * (r : ℝ) * (4 * (ζ : ℝ) ^ 4) / α := by ring
      _ ≤ 1250 * K * (r : ℝ) * (ζ : ℝ) ^ 6 / α := by gcongr
      _ = (10000 * K * (r : ℝ) * (ζ : ℝ) ^ 6 / α) / 8 := by ring
      _ ≤ (n₀ : ℝ) / 8 := by linarith
  have hJ_card_ge : (n₀ : ℝ) / 2 ≤ (J_elig.card : ℝ) := by
    have hsub_union : V_G0 ⊆ J_elig ∪ Finset.univ.biUnion F := by
      intro x hx
      by_cases hxF : x ∈ Finset.univ.biUnion F
      · exact Finset.mem_union_right _ hxF
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxF⟩)
    have hcard_nat : V_G0.card ≤ J_elig.card + (2 * k) * D := by
      calc
        V_G0.card ≤ (J_elig ∪ Finset.univ.biUnion F).card := Finset.card_le_card hsub_union
        _ ≤ J_elig.card + (Finset.univ.biUnion F).card := Finset.card_union_le _ _
        _ ≤ J_elig.card + (2 * k) * D := Nat.add_le_add_left hF_biUnion_le _
    have hcard_real : (V_G0.card : ℝ) ≤ (J_elig.card : ℝ) + 2 * (k : ℝ) * (D : ℝ) := by
      exact_mod_cast hcard_nat
    linarith
  have hm_ge1 : 1 ≤ J_elig.card := by
    have h1 : (1 : ℝ) ≤ (J_elig.card : ℝ) := by linarith
    exact_mod_cast h1
  obtain ⟨I_center, hIc_sub, hIc_card, hIc_disj⟩ :=
    conflict_indep_extraction S V_G0 colOf V_virt F hsplit hsparse Finset.sdiff_subset hm_ge1
  refine ⟨k', colOf, V_virt, F, I_center, hk'_le, hsplit, hIc_sub, ?_, hIc_disj⟩
  have hΔ_le : (Δ : ℝ) ≤ 2 * (ζ : ℝ) * (n₀ : ℝ) / (k : ℝ) := by
    have hceil : (Δ : ℝ) ≤ (ζ : ℝ) * (n₀ : ℝ) / (k : ℝ) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    calc
      (Δ : ℝ) ≤ (ζ : ℝ) * (n₀ : ℝ) / (k : ℝ) + (ζ : ℝ) * (n₀ : ℝ) / (k : ℝ) := by linarith
      _ = 2 * (ζ : ℝ) * (n₀ : ℝ) / (k : ℝ) := by ring
  have h1_plus_ζΔ : 1 + (ζ : ℝ) * (Δ : ℝ) ≤ 3 * (ζ : ℝ) ^ 2 * (n₀ : ℝ) / (k : ℝ) := by
    have h1_le : (1 : ℝ) ≤ (ζ : ℝ) ^ 2 * (n₀ : ℝ) / (k : ℝ) := by
      calc
        (1 : ℝ) ≤ 1 * ((ζ : ℝ) * (n₀ : ℝ) / (k : ℝ)) := by linarith
        _ ≤ (ζ : ℝ) * ((ζ : ℝ) * (n₀ : ℝ) / (k : ℝ)) := by gcongr; linarith
        _ = (ζ : ℝ) ^ 2 * (n₀ : ℝ) / (k : ℝ) := by ring
    have hζΔ_le : (ζ : ℝ) * (Δ : ℝ) ≤ 2 * (ζ : ℝ) ^ 2 * (n₀ : ℝ) / (k : ℝ) := by
      calc
        (ζ : ℝ) * (Δ : ℝ) ≤ (ζ : ℝ) * (2 * (ζ : ℝ) * (n₀ : ℝ) / (k : ℝ)) := by gcongr
        _ = 2 * (ζ : ℝ) ^ 2 * (n₀ : ℝ) / (k : ℝ) := by ring
    calc
      1 + (ζ : ℝ) * (Δ : ℝ)
          ≤ (ζ : ℝ) ^ 2 * (n₀ : ℝ) / (k : ℝ) + 2 * (ζ : ℝ) ^ 2 * (n₀ : ℝ) / (k : ℝ) := by
            linarith
      _ = 3 * (ζ : ℝ) ^ 2 * (n₀ : ℝ) / (k : ℝ) := by ring
  have hn₀_pos : (0 : ℝ) < (n₀ : ℝ) := by linarith
  have hfrac_eq :
      ((n₀ : ℝ) / 2) / (3 * (ζ : ℝ) ^ 2 * (n₀ : ℝ) / (k : ℝ)) =
        (k : ℝ) / (6 * (ζ : ℝ) ^ 2) := by
    field_simp
    ring
  have hlow1 :
      (1 / 10 : ℝ) * (r : ℝ) / (ζ : ℝ) ^ 5 ≤ (k : ℝ) / (6 * (ζ : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hrk_real : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrk
    have hζ3_ge1 : (1 : ℝ) ≤ (ζ : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    calc
      (1 / 10 : ℝ) * (r : ℝ) * (6 * (ζ : ℝ) ^ 2)
          = (3 / 5 : ℝ) * (r : ℝ) * (ζ : ℝ) ^ 2 := by ring
      _ ≤ 1 * (k : ℝ) * (ζ : ℝ) ^ 2 := by
            have h35 : (3 / 5 : ℝ) ≤ 1 := by norm_num
            gcongr
      _ ≤ (ζ : ℝ) ^ 3 * (k : ℝ) * (ζ : ℝ) ^ 2 := by gcongr
      _ = (k : ℝ) * (ζ : ℝ) ^ 5 := by ring
  have hlow2 :
      (k : ℝ) / (6 * (ζ : ℝ) ^ 2) ≤
        (J_elig.card : ℝ) / (1 + (ζ : ℝ) * (Δ : ℝ)) := by
    rw [← hfrac_eq]
    refine le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) h1_plus_ζΔ) ?_
    exact div_le_div_of_nonneg_right hJ_card_ge (by positivity)
  exact hlow1.trans (hlow2.trans hIc_card)

end Osi.LowerBound
