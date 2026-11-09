import Osi.Spec
import Osi.Prelim.Hypergeom

/-!
# Section 8.2: Subsampled `C₄`-Free Subgraph `G₀` (`Lemma 8.3`)

Proves `Lemma_8_3_C4FreeSubgraph` together with the automatic `C₄`-free pair-counting bound
`|V_G0| ≤ k (k - 1) / 2` whenever every row in `V_G0` has support size `≥ 2`.
-/

namespace Osi.LowerBound

open Osi.Spec

/-- Deterministic `C₄`-free pair bound: if `V_G0 ⊆ [n]` is `C₄`-free (`IsC4FreeRows S V_G0`) and
every row `i ∈ V_G0` has `2 ≤ (rowSupport S i).card`, then choosing a 2-element subset of
`rowSupport S i` injects `V_G0` into `(Finset.univ : Finset (Fin k)).powersetCard 2`, so
`2 * V_G0.card ≤ k * (k - 1)` (in particular `(V_G0.card : ℝ) ≤ (k : ℝ) ^ 2 / 2`). -/
theorem c4Free_card_le_pairs {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (V_G0 : Finset (Fin n))
    (hc4 : IsC4FreeRows S V_G0)
    (hdeg : ∀ i ∈ V_G0, 2 ≤ (rowSupport S i).card) :
    2 * V_G0.card ≤ k * (k - 1) := by
  let p : Fin n → Finset (Fin k) := fun i =>
    if h : ((rowSupport S i).powersetCard 2).Nonempty then h.choose else ∅
  have hp_mem : ∀ {i : Fin n}, i ∈ V_G0 → p i ∈ (rowSupport S i).powersetCard 2 := by
    intro i hi
    have hne : ((rowSupport S i).powersetCard 2).Nonempty :=
      Finset.powersetCard_nonempty.mpr (hdeg i hi)
    simpa only [p, dif_pos hne] using hne.choose_spec
  have hmaps : Set.MapsTo p V_G0 ((Finset.univ : Finset (Fin k)).powersetCard 2) := by
    intro i hi
    have hpi := Finset.mem_powersetCard.mp (hp_mem hi)
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hpi.2⟩
  have hinj : (V_G0 : Set (Fin n)).InjOn p := by
    intro u hu v hv hpuv
    by_contra huv
    have hpu := Finset.mem_powersetCard.mp (hp_mem hu)
    have hpv := Finset.mem_powersetCard.mp (hp_mem hv)
    have hpv_sub : p u ⊆ rowSupport S v := by
      rw [hpuv]
      exact hpv.1
    have hsub : p u ⊆ rowSupport S u ∩ rowSupport S v :=
      Finset.subset_inter hpu.1 hpv_sub
    have h2 : 2 ≤ (rowSupport S u ∩ rowSupport S v).card := by
      have hle := Finset.card_le_card hsub
      omega
    have h1 : (rowSupport S u ∩ rowSupport S v).card ≤ 1 := hc4 u hu v hv huv
    omega
  have hcard : V_G0.card ≤ ((Finset.univ : Finset (Fin k)).powersetCard 2).card :=
    Finset.card_le_card_of_injOn p hmaps hinj
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Nat.choose_two_right] at hcard
  omega

private lemma mem_cleanRows_props {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) {α M : ℝ}
    (hα : 0 < α) {i : Fin n} (hi : i ∈ cleanRows S α M) :
    α ≤ vecSqNorm (S i) ∧ vecSqNorm (S i) ≤ M ∧ 2 ≤ (rowSupport S i).card := by
  have hnot_heavy : i ∉ heavyRows S M := by
    intro h
    simp [cleanRows, h] at hi
  have hnot_small : i ∉ smallRows S α := by
    intro h
    simp [cleanRows, h] at hi
  have hnot_one : i ∉ oneSparseRows S := by
    intro h
    simp [cleanRows, h] at hi
  have hle_M : vecSqNorm (S i) ≤ M := by
    simpa [heavyRows] using hnot_heavy
  have hle_α : α ≤ vecSqNorm (S i) := by
    simpa [smallRows] using hnot_small
  have hne1 : (rowSupport S i).card ≠ 1 := by
    simpa [oneSparseRows] using hnot_one
  have hne0 : (rowSupport S i).card ≠ 0 := by
    intro h0
    have hemp : rowSupport S i = ∅ := Finset.card_eq_zero.mp h0
    have hzero_vec : ∀ j : Fin k, S i j = 0 := by
      intro j
      by_contra hj
      have hmem : j ∈ rowSupport S i := by simp [rowSupport, hj]
      simp [hemp] at hmem
    have hnorm0 : vecSqNorm (S i) = 0 := by
      simp [vecSqNorm, hzero_vec]
    linarith
  exact ⟨hle_α, hle_M, by omega⟩

private lemma isC4FreeRows_prunedRows {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (α M : ℝ)
    (V₀ : Finset (Fin n)) :
    IsC4FreeRows S (prunedRows S α M V₀) := by
  intro u hu v hv huv
  have hu_mem : u ∈ V₀ ∩ cleanRows S α M ∧
      ∀ w ∈ V₀ ∩ cleanRows S α M, w < u → (rowSupport S w ∩ rowSupport S u).card ≤ 1 := by
    simpa only [prunedRows, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hu
  have hv_mem : v ∈ V₀ ∩ cleanRows S α M ∧
      ∀ w ∈ V₀ ∩ cleanRows S α M, w < v → (rowSupport S w ∩ rowSupport S v).card ≤ 1 := by
    simpa only [prunedRows, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hv
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact hv_mem.2 u hu_mem.1 hlt
  · rw [Finset.inter_comm]
    exact hu_mem.2 v hv_mem.1 hgt

private lemma card_sdiff_prunedRows_le {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (α M : ℝ)
    (V₀ : Finset (Fin n)) :
    ((V₀ ∩ cleanRows S α M) \ prunedRows S α M V₀).card ≤ (subCollidingPairs S V₀).card := by
  classical
  let C : Finset (Fin n) := V₀ ∩ cleanRows S α M
  let bad : Fin n → Prop := fun v =>
    ∃ u : Fin n, u ∈ C ∧ u < v ∧ 2 ≤ (rowSupport S u ∩ rowSupport S v).card
  let f : Fin n → Fin n × Fin n := fun v =>
    if h : bad v then (h.choose, v) else (v, v)
  have hf_snd : ∀ v : Fin n, (f v).2 = v := by
    intro v
    by_cases h : bad v <;> simp [f, h]
  have hinj : (((C \ prunedRows S α M V₀) : Finset (Fin n)) : Set (Fin n)).InjOn f := by
    intro v₁ _ v₂ _ hfv
    have h2 := congrArg Prod.snd hfv
    simpa only [hf_snd] using h2
  have hmaps :
      Set.MapsTo f (((C \ prunedRows S α M V₀) : Finset (Fin n)) : Set (Fin n))
        ((subCollidingPairs S V₀ : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)) := by
    intro v hv
    have hv_fin : v ∈ C \ prunedRows S α M V₀ := Finset.mem_coe.mp hv
    have hv' : v ∈ C ∧ v ∉ prunedRows S α M V₀ := Finset.mem_sdiff.mp hv_fin
    have hbad : bad v := by
      by_contra hnbad
      have hpruned : v ∈ prunedRows S α M V₀ := by
        simp only [prunedRows, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        refine ⟨hv'.1, ?_⟩
        intro u hu hlt
        by_contra hgt1
        exact hnbad ⟨u, hu, hlt, by omega⟩
      exact hv'.2 hpruned
    rcases hbad.choose_spec with ⟨huC, hlt, hcard2⟩
    have huV₀ : hbad.choose ∈ V₀ := (Finset.mem_inter.mp huC).1
    have hvV₀ : v ∈ V₀ := (Finset.mem_inter.mp hv'.1).1
    rw [Finset.mem_coe]
    simp only [subCollidingPairs, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, f, dif_pos hbad]
    exact ⟨huV₀, hvV₀, hlt, hcard2⟩
  exact Finset.card_le_card_of_injOn f hmaps hinj

private lemma prunedRows_card_ge {n k n₀ : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (α M : ℝ)
    (V₀ : Finset (Fin n)) (hcard : V₀.card = n₀)
    (hbad1 : ((V₀ \ cleanRows S α M).card : ℝ) ≤ (n₀ : ℝ) / 4)
    (hbad2 : ((subCollidingPairs S V₀).card : ℝ) ≤ (n₀ : ℝ) / 16) :
    (5 / 8 : ℝ) * (n₀ : ℝ) ≤ ((prunedRows S α M V₀).card : ℝ) := by
  have hsub : prunedRows S α M V₀ ⊆ V₀ ∩ cleanRows S α M := by
    intro v hv
    simp only [prunedRows, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hv
    exact hv.1
  have hpart1 : (V₀ \ cleanRows S α M).card + (V₀ ∩ cleanRows S α M).card = V₀.card :=
    Finset.card_sdiff_add_card_inter V₀ (cleanRows S α M)
  have hpart2 :
      ((V₀ ∩ cleanRows S α M) \ prunedRows S α M V₀).card + (prunedRows S α M V₀).card =
        (V₀ ∩ cleanRows S α M).card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hcoll := card_sdiff_prunedRows_le S α M V₀
  have hnat :
      n₀ ≤ (V₀ \ cleanRows S α M).card + (subCollidingPairs S V₀).card +
        (prunedRows S α M V₀).card := by
    omega
  have hreal :
      (n₀ : ℝ) ≤ ((V₀ \ cleanRows S α M).card : ℝ) + ((subCollidingPairs S V₀).card : ℝ) +
        ((prunedRows S α M V₀).card : ℝ) := by
    exact_mod_cast hnat
  have hn₀_nonneg : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg n₀
  linarith

private lemma subCollidingPairs_eq_filter {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (V₀ : Finset (Fin n)) :
    subCollidingPairs S V₀ =
      (overlapPairs S).filter (fun uv => uv.1 ∈ V₀ ∧ uv.2 ∈ V₀) := by
  ext uv
  simp only [subCollidingPairs, overlapPairs, Finset.mem_filter,
    Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  tauto

private lemma bad_clean_prob_le {n k n₀ : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (α : ℝ)
    (hn₀ : 1024 ≤ n₀) (hle : n₀ ≤ n)
    (hclean : (13 / 16 : ℝ) * (n : ℝ) ≤ ((cleanRows S α 160).card : ℝ)) :
    uniformSubsetProb n n₀
        (fun V₀ => (n₀ : ℝ) / 4 < ((V₀ \ cleanRows S α 160).card : ℝ)) ≤ 1 / 16 := by
  let B : Finset (Fin n) := (cleanRows S α 160)ᶜ
  let μ : ℝ := (n₀ : ℝ) * (B.card : ℝ) / (n : ℝ)
  let t : ℝ := (n₀ : ℝ) / 16
  have hn₀_1024 : (1024 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
  have hn₀_pos : (0 : ℝ) < (n₀ : ℝ) := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have hn_1024 : 1024 ≤ n := le_trans hn₀ hle
    have hn_real : (1024 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_1024
    linarith
  have ht_pos : 0 < t := by positivity
  have hsum_nat : B.card + (cleanRows S α 160).card = n := by
    dsimp only [B]
    rw [Finset.compl_eq_univ_sdiff, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin]
  have hsum_real : (B.card : ℝ) + ((cleanRows S α 160).card : ℝ) = (n : ℝ) := by
    exact_mod_cast hsum_nat
  have hB_le : (B.card : ℝ) ≤ (3 / 16 : ℝ) * (n : ℝ) := by linarith
  have hμ_le : μ ≤ (3 / 16 : ℝ) * (n₀ : ℝ) := by
    calc
      μ = (n₀ : ℝ) * (B.card : ℝ) / (n : ℝ) := rfl
      _ ≤ (n₀ : ℝ) * ((3 / 16 : ℝ) * (n : ℝ)) / (n : ℝ) := by gcongr
      _ = (3 / 16 : ℝ) * (n₀ : ℝ) := by field_simp
  have hmono :
      uniformSubsetProb n n₀ (fun V₀ => (n₀ : ℝ) / 4 < ((V₀ \ cleanRows S α 160).card : ℝ)) ≤
        uniformSubsetProb n n₀ (fun V₀ => μ + t ≤ ((V₀ ∩ B).card : ℝ)) := by
    apply Osi.Prelim.uniformSubsetProb_mono
    intro V₀ _ hlt
    rw [Finset.sdiff_eq_inter_compl] at hlt
    change (n₀ : ℝ) / 4 < ((V₀ ∩ B).card : ℝ) at hlt
    have ht_def : t = (n₀ : ℝ) / 16 := rfl
    linarith
  have hcheb :
      uniformSubsetProb n n₀ (fun V₀ => μ + t ≤ ((V₀ ∩ B).card : ℝ)) ≤ μ / t ^ 2 :=
    Osi.Prelim.uniformSubsetProb_inter_card_chebyshev (by omega) hle B t ht_pos
  have hbound : μ / t ^ 2 ≤ 1 / 16 := by
    calc
      μ / t ^ 2 ≤ ((3 / 16 : ℝ) * (n₀ : ℝ)) / ((n₀ : ℝ) / 16) ^ 2 := by gcongr
      _ = 48 / (n₀ : ℝ) := by
        field_simp
        norm_num
      _ ≤ 48 / 1024 := by gcongr
      _ ≤ 1 / 16 := by norm_num
  linarith

private lemma bad_colliding_prob_le {n k r ζ n₀ : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (C_samp α : ℝ) (hCsamp : 1024 ≤ C_samp) (hα0 : 0 < α)
    (hr1 : 1 ≤ r) (hrk : r ≤ k) (hζ1 : 1 ≤ ζ)
    (hov : SatisfiesOverlapCond S (((512 * C_samp / α) * (ζ : ℝ) ^ 6)⁻¹))
    (hn₀ : 1024 ≤ n₀)
    (hn₀_ceil : (n₀ : ℝ) - 1 ≤ C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α)
    (hle : n₀ ≤ n) :
    uniformSubsetProb n n₀
        (fun V₀ => (n₀ : ℝ) / 16 < ((subCollidingPairs S V₀).card : ℝ)) ≤ 1 / 16 := by
  let P : Finset (Fin n × Fin n) := overlapPairs S
  let t : ℝ := (n₀ : ℝ) / 16
  have hn₀_real : (1024 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
  have hn₀_pos : (0 : ℝ) < (n₀ : ℝ) := by linarith
  have hn_1024 : 1024 ≤ n := le_trans hn₀ hle
  have hn_real : (1024 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_1024
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have hk1 : 1 ≤ k := le_trans hr1 hrk
    have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hζ_pos : (0 : ℝ) < (ζ : ℝ) := by
    have hζ_real : (1 : ℝ) ≤ (ζ : ℝ) := by exact_mod_cast hζ1
    linarith
  have hCsamp_pos : 0 < C_samp := by linarith
  have ht_pos : 0 < t := by positivity
  have hP_ne : ∀ uv ∈ P, uv.1 ≠ uv.2 := by
    intro uv huv
    simp only [P, overlapPairs, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at huv
    exact ne_of_lt huv.1
  have hmono :
      uniformSubsetProb n n₀
          (fun V₀ => (n₀ : ℝ) / 16 < ((subCollidingPairs S V₀).card : ℝ)) ≤
        uniformSubsetProb n n₀
          (fun V₀ => t ≤ ((P.filter (fun uv => uv.1 ∈ V₀ ∧ uv.2 ∈ V₀)).card : ℝ)) := by
    apply Osi.Prelim.uniformSubsetProb_mono
    intro V₀ _ hlt
    rw [subCollidingPairs_eq_filter] at hlt
    exact le_of_lt hlt
  have hmarkov :
      uniformSubsetProb n n₀
          (fun V₀ => t ≤ ((P.filter (fun uv => uv.1 ∈ V₀ ∧ uv.2 ∈ V₀)).card : ℝ)) ≤
        ((P.card : ℝ) * ((n₀ : ℝ) * ((n₀ : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1))) / t :=
    Osi.Prelim.uniformSubsetProb_pairs_markov (by omega) hle P hP_ne t ht_pos
  have hsimp :
      ((P.card : ℝ) * ((n₀ : ℝ) * ((n₀ : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1))) / t =
        16 * (overlapPairCount S : ℝ) * ((n₀ : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    change (((overlapPairCount S : ℝ) * ((n₀ : ℝ) * ((n₀ : ℝ) - 1)) /
        ((n : ℝ) * ((n : ℝ) - 1))) / ((n₀ : ℝ) / 16)) = _
    field_simp
  have hov' :
      (overlapPairCount S : ℝ) ≤ α * (n : ℝ) ^ 2 / (512 * C_samp * (ζ : ℝ) ^ 6 * (k : ℝ)) := by
    calc
      (overlapPairCount S : ℝ) ≤
          (((512 * C_samp / α) * (ζ : ℝ) ^ 6)⁻¹) * ((n : ℝ) ^ 2 / (k : ℝ)) := hov
      _ = α * (n : ℝ) ^ 2 / (512 * C_samp * (ζ : ℝ) ^ 6 * (k : ℝ)) := by field_simp
  have hn₀1_nonneg : (0 : ℝ) ≤ (n₀ : ℝ) - 1 := by linarith
  have hprod :
      (overlapPairCount S : ℝ) * ((n₀ : ℝ) - 1) ≤ ((n : ℝ) ^ 2 * (r : ℝ)) / (512 * (k : ℝ)) := by
    calc
      (overlapPairCount S : ℝ) * ((n₀ : ℝ) - 1) ≤
          (α * (n : ℝ) ^ 2 / (512 * C_samp * (ζ : ℝ) ^ 6 * (k : ℝ))) *
            (C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α) :=
        mul_le_mul hov' hn₀_ceil hn₀1_nonneg (by positivity)
      _ = ((n : ℝ) ^ 2 * (r : ℝ)) / (512 * (k : ℝ)) := by field_simp
  have hrk_real : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrk
  have hprod2 :
      (overlapPairCount S : ℝ) * ((n₀ : ℝ) - 1) ≤ (n : ℝ) ^ 2 / 512 := by
    calc
      (overlapPairCount S : ℝ) * ((n₀ : ℝ) - 1) ≤ ((n : ℝ) ^ 2 * (r : ℝ)) / (512 * (k : ℝ)) :=
        hprod
      _ ≤ ((n : ℝ) ^ 2 * (k : ℝ)) / (512 * (k : ℝ)) := by gcongr
      _ = (n : ℝ) ^ 2 / 512 := by field_simp
  have hnum :
      16 * (overlapPairCount S : ℝ) * ((n₀ : ℝ) - 1) ≤
        (1 / 16 : ℝ) * ((n : ℝ) * ((n : ℝ) - 1)) := by
    have h1 : 16 * (overlapPairCount S : ℝ) * ((n₀ : ℝ) - 1) ≤ (1 / 32 : ℝ) * (n : ℝ) ^ 2 := by
      linarith
    have h2 : (0 : ℝ) ≤ (1 / 32 : ℝ) * (n : ℝ) * ((n : ℝ) - 2) :=
      mul_nonneg (by positivity) (by linarith)
    have h3 :
        (1 / 16 : ℝ) * ((n : ℝ) * ((n : ℝ) - 1)) - (1 / 32 : ℝ) * (n : ℝ) ^ 2 =
          (1 / 32 : ℝ) * (n : ℝ) * ((n : ℝ) - 2) := by
      ring
    linarith
  have hdiv :
      16 * (overlapPairCount S : ℝ) * ((n₀ : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 / 16 := by
    rw [div_le_iff₀ (mul_pos hn_pos hn1_pos)]
    exact hnum
  linarith

/-- **Lemma 8.3 (`C₄`-free subsampled subgraph `G₀`, p. 38).** -/
theorem lemma_8_3_C4FreeSubgraph : Lemma_8_3_C4FreeSubgraph := by
  refine ⟨1024, by norm_num, ?_⟩
  intro C_samp α n k r ζ S hCsamp hα0 hα1 hr1 hrk hζ1 hsparse hov hclean n₀ hn₀_eq hn₀_le
  let X : ℝ := C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α
  have hr_real : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hζ_real : (1 : ℝ) ≤ (ζ : ℝ) := by exact_mod_cast hζ1
  have hζ6_ge1 : (1 : ℝ) ≤ (ζ : ℝ) ^ 6 := one_le_pow₀ hζ_real
  have hX_ge : 1024 ≤ X := by
    dsimp [X]
    rw [le_div_iff₀ hα0]
    have h1 : (1024 : ℝ) * α ≤ 1024 := by linarith
    have h2 : (1024 : ℝ) ≤ C_samp * (r : ℝ) := by nlinarith
    have h3 : C_samp * (r : ℝ) ≤ C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 :=
      le_mul_of_one_le_right (by positivity) hζ6_ge1
    linarith
  have hX_nonneg : 0 ≤ X := by linarith
  have hn₀_real_ge : (1024 : ℝ) ≤ (n₀ : ℝ) := by
    have hceil : X ≤ (n₀ : ℝ) := by
      rw [hn₀_eq]
      exact Nat.le_ceil X
    linarith
  have hn₀_1024 : 1024 ≤ n₀ := by exact_mod_cast hn₀_real_ge
  have hn₀_ceil : (n₀ : ℝ) - 1 ≤ X := by
    have hlt : (n₀ : ℝ) < X + 1 := by
      rw [hn₀_eq]
      exact Nat.ceil_lt_add_one hX_nonneg
    linarith
  let E_good : Finset (Fin n) → Prop := fun V₀ =>
    (((V₀ \ cleanRows S α 160).card : ℝ) ≤ (n₀ : ℝ) / 4) ∧
      (((subCollidingPairs S V₀).card : ℝ) ≤ (n₀ : ℝ) / 16)
  have hnot_good_le : uniformSubsetProb n n₀ (fun V₀ => ¬ E_good V₀) ≤ 1 / 8 := by
    have hmono_or :
        uniformSubsetProb n n₀ (fun V₀ => ¬ E_good V₀) ≤
          uniformSubsetProb n n₀
            (fun V₀ =>
              ((n₀ : ℝ) / 4 < ((V₀ \ cleanRows S α 160).card : ℝ)) ∨
                ((n₀ : ℝ) / 16 < ((subCollidingPairs S V₀).card : ℝ))) := by
      apply Osi.Prelim.uniformSubsetProb_mono
      intro V₀ _ hnot
      dsimp only [E_good] at hnot
      rcases not_and_or.mp hnot with h1 | h2
      · exact Or.inl (lt_of_not_ge h1)
      · exact Or.inr (lt_of_not_ge h2)
    have hunion :=
      Osi.Prelim.uniformSubsetProb_or_le (r := n₀)
        (fun V₀ => (n₀ : ℝ) / 4 < ((V₀ \ cleanRows S α 160).card : ℝ))
        (fun V₀ => (n₀ : ℝ) / 16 < ((subCollidingPairs S V₀).card : ℝ))
    have hb1 := bad_clean_prob_le S α hn₀_1024 hn₀_le hclean
    have hb2 := bad_colliding_prob_le S C_samp α hCsamp hα0 hr1 hrk hζ1 hov hn₀_1024 hn₀_ceil hn₀_le
    linarith
  have hgood_ge : (7 / 8 : ℝ) ≤ uniformSubsetProb n n₀ E_good := by
    have hcompl := Osi.Prelim.uniformSubsetProb_compl hn₀_le E_good
    linarith
  refine le_trans hgood_ge (Osi.Prelim.uniformSubsetProb_mono ?_)
  intro V₀ hV₀_card hgood
  refine ⟨hgood.1, hgood.2, ?_, ?_, ?_⟩
  · exact prunedRows_card_ge S α 160 V₀ hV₀_card hgood.1 hgood.2
  · exact isC4FreeRows_prunedRows S α 160 V₀
  · intro i hi
    have hi_clean : i ∈ cleanRows S α 160 := by
      simp only [prunedRows, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hi
      exact (Finset.mem_inter.mp hi.1).2
    rcases mem_cleanRows_props S hα0 hi_clean with ⟨hα_le, h160_le, hdeg2⟩
    exact ⟨hα_le, h160_le, hdeg2, hsparse i⟩

end Osi.LowerBound
