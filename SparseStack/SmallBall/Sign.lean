import SparseStack.SmallBall.Defs

/-!
# Small ball, sign step (paper lines 249–295)

Fix the hashes `x` with `𝓛 ≤ s/16`.

* `retained_total`: buckets with `W_{tu} > 20/D` have `W_{tu} ≤ 2 (W_{tu} - 10/D)_+`, so they
  carry total mass at most `2 𝓛 ≤ s/8`; the retained masses `v_{tu}` (`retainedMass`) satisfy
  `V = ∑ v_{tu} ≥ s - s/8 = 7s/8` and `v_{tu} ≤ 20/D`.
* For each bucket `j = (t, u)`, the event `E_j = {a² v_j/3 ≤ Y_j²}` (with `Y_j = bucketOut`) is
  determined by the signs of the block `S_j = {(t, i) : h_t(i) = u}`; the blocks are pairwise
  disjoint. `Y_j` is a Rademacher sum with `∑ c_k² = ∑_{bucket} w_i² ≥ a² W_j ≥ a² v_j`
  (disjoint supports of `h` and `z`), so `P(E_j) ≥ 4/27` (`rademacher_smallball`).
* `weighted_bernoulli_lower_tail` (`π = 4/27`, `κ' = 8/81`) bounds
  `P{∑ v_j 1_{E_j} < (8/81) V} ≤ exp(-(11/1296) V/(20/D)) ≤ e^{-sD/3200}`; outside this event
  `‖Π w‖² ≥ (a²/(3s)) (8/81) V ≥ 2a²/81`.
-/

open scoped BigOperators

namespace SparseStack

open SparseFock

noncomputable section

namespace SmallBallAux

/-- A sum over `Fin s × Fin n` supported on the block `t`. -/
theorem sum_prod_single {s n : ℕ} (t : Fin s) (F : Fin s × Fin n → ℝ)
    (hF : ∀ k : Fin s × Fin n, k.1 ≠ t → F k = 0) : ∑ k, F k = ∑ i, F (t, i) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single t]
  · intro t' _ ht'
    exact Finset.sum_eq_zero (fun i _ => hF (t', i) ht')
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem retainedMass_nonneg {s b n : ℕ} (z : Fin n → ℝ) (D : ℝ) (x : Fin s × Fin n → Fin b)
    (t : Fin s) (u : Fin b) : 0 ≤ retainedMass z D x t u := by
  unfold retainedMass
  split_ifs
  · exact bucketMass_nonneg z x t u
  · exact le_rfl

theorem retainedMass_le {s b n : ℕ} (z : Fin n → ℝ) {D : ℝ} (hD : 0 < D)
    (x : Fin s × Fin n → Fin b) (t : Fin s) (u : Fin b) : retainedMass z D x t u ≤ 20 / D := by
  unfold retainedMass
  split_ifs with h
  · exact h
  · positivity

theorem retainedMass_le_bucketMass {s b n : ℕ} (z : Fin n → ℝ) (D : ℝ)
    (x : Fin s × Fin n → Fin b) (t : Fin s) (u : Fin b) :
    retainedMass z D x t u ≤ bucketMass z x t u := by
  unfold retainedMass
  split_ifs
  · exact le_rfl
  · exact bucketMass_nonneg z x t u

/-- On `𝓛 ≤ s/16` the retained buckets carry total mass `V ≥ 7s/8` (paper lines 249–254). -/
theorem retained_total {s b n : ℕ} (z : Fin n → ℝ) (hz1 : ∑ i, z i ^ 2 = 1) (D : ℝ)
    (x : Fin s × Fin n → Fin b) (hx : excessMass z D x ≤ (s : ℝ) / 16) :
    7 * (s : ℝ) / 8 ≤ ∑ t, ∑ u, retainedMass z D x t u := by
  have hgap : ∀ t u, bucketMass z x t u - retainedMass z D x t u ≤
      2 * max (bucketMass z x t u - 10 / D) 0 := by
    intro t u
    unfold retainedMass
    split_ifs with hle
    · have := le_max_right (bucketMass z x t u - 10 / D) 0
      linarith
    · push Not at hle
      have := le_max_left (bucketMass z x t u - 10 / D) 0
      have h20 : (20 : ℝ) / D = 2 * (10 / D) := by ring
      linarith
  have h1 : ∑ t : Fin s, ∑ u : Fin b, bucketMass z x t u = s := by
    simp only [sum_bucketMass z hz1 x, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have h2 : ∑ t : Fin s, ∑ u : Fin b, (bucketMass z x t u - retainedMass z D x t u) ≤
      2 * excessMass z D x := by
    unfold excessMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    exact hgap t u
  simp only [Finset.sum_sub_distrib] at h2
  linarith

/-- Sign step (paper lines 257–291): for fixed hashes with `𝓛 ≤ s/16`, the probability over
the signs that `‖Π w‖² < (2/81) a²` is at most `e^{-sD/3200}`. -/
theorem sign_step {s b n : ℕ} (hs : 0 < s) (h z : Fin n → ℝ) (a : ℝ) (ha : 0 < a)
    (hdisj : ∀ i, h i = 0 ∨ z i = 0) (hz1 : ∑ i, z i ^ 2 = 1) (D : ℝ) (hD1 : 1 ≤ D)
    (x : Fin s × Fin n → Fin b) (hx : excessMass z D x ≤ (s : ℝ) / 16) :
    (signLaw s n).prob
        {y | 1 / (s : ℝ) * ∑ t, ∑ u, bucketOut (h + a • z) x y t u ^ 2 < 2 / 81 * a ^ 2} ≤
      Real.exp (-((s : ℝ) * D) / 3200) := by
  have hD : 0 < D := by linarith
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  set w : Fin n → ℝ := h + a • z with hw
  -- `w_i² = h_i² + a² z_i² ≥ a² z_i²` (disjoint supports)
  have hw2 : ∀ i, a ^ 2 * z i ^ 2 ≤ w i ^ 2 := by
    intro i
    have hwi : w i = h i + a * z i := rfl
    rw [hwi]
    rcases hdisj i with hi | hi
    · rw [hi]
      nlinarith [sq_nonneg (a * z i)]
    · rw [hi]
      nlinarith [sq_nonneg (h i)]
  -- weights, events and blocks
  let v : Fin s × Fin b → ℝ := fun j => retainedMass z D x j.1 j.2
  let E : Fin s × Fin b → Set (Fin s × Fin n → Bool) :=
    fun j => {y | a ^ 2 * v j / 3 ≤ bucketOut w x y j.1 j.2 ^ 2}
  let S : Fin s × Fin b → Finset (Fin s × Fin n) :=
    fun j => Finset.univ.filter (fun k => k.1 = j.1 ∧ x k = j.2)
  have hS : Pairwise (fun j k => Disjoint (S j) (S k)) := by
    intro j k hjk
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hm1 hm2
    exact hjk (Prod.ext (hm1.1.symm.trans hm2.1) (hm1.2.symm.trans hm2.2))
  have hE : ∀ j y y', (∀ k ∈ S j, y k = y' k) → (y ∈ E j ↔ y' ∈ E j) := by
    intro j y y' hyy
    have hout : bucketOut w x y j.1 j.2 = bucketOut w x y' j.1 j.2 := by
      unfold bucketOut
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : x (j.1, i) = j.2
      · have hmem : (j.1, i) ∈ S j := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hi
        rw [if_pos hi, if_pos hi, hyy (j.1, i) hmem]
      · rw [if_neg hi, if_neg hi]
    show a ^ 2 * v j / 3 ≤ bucketOut w x y j.1 j.2 ^ 2 ↔
      a ^ 2 * v j / 3 ≤ bucketOut w x y' j.1 j.2 ^ 2
    rw [hout]
  have hπ : ∀ j, 4 / 27 ≤ (signLaw s n).prob (E j) := by
    intro j
    obtain ⟨t, u⟩ := j
    let c : Fin s × Fin n → ℝ := fun k => if k.1 = t then (if x k = u then w k.2 else 0) else 0
    have hct : ∀ i, c (t, i) = if x (t, i) = u then w i else 0 := fun i => if_pos rfl
    have hc0 : ∀ k : Fin s × Fin n, k.1 ≠ t → c k = 0 := fun k hk => if_neg hk
    have hY : ∀ y : Fin s × Fin n → Bool, ∑ k, c k * signValue (y k) = bucketOut w x y t u := by
      intro y
      rw [sum_prod_single t (fun k => c k * signValue (y k))
        (fun k hk => by show c k * signValue (y k) = 0; rw [hc0 k hk, zero_mul])]
      unfold bucketOut
      apply Finset.sum_congr rfl
      intro i _
      show c (t, i) * signValue (y (t, i)) = _
      rw [hct i]
      split_ifs <;> ring
    have hc2 : a ^ 2 * v (t, u) ≤ ∑ k, c k ^ 2 := by
      rw [sum_prod_single t (fun k => c k ^ 2)
        (fun k hk => by show c k ^ 2 = 0; rw [hc0 k hk]; ring)]
      calc a ^ 2 * v (t, u) ≤ a ^ 2 * bucketMass z x t u :=
            mul_le_mul_of_nonneg_left (retainedMass_le_bucketMass z D x t u) (sq_nonneg a)
        _ = ∑ i, (if x (t, i) = u then a ^ 2 * z i ^ 2 else 0) := by
            unfold bucketMass
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> ring
        _ ≤ ∑ i, c (t, i) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            rw [hct i]
            split_ifs
            · exact hw2 i
            · norm_num
    calc (4 : ℝ) / 27 ≤ (signsLaw (Fin s × Fin n)).prob
          {y | (∑ k, c k ^ 2) / 3 ≤ (∑ k, c k * signValue (y k)) ^ 2} := rademacher_smallball c
      _ ≤ (signLaw s n).prob (E (t, u)) := by
          apply FiniteLaw.prob_mono
          intro y hy
          have hy' : (∑ k, c k ^ 2) / 3 ≤ (∑ k, c k * signValue (y k)) ^ 2 := hy
          rw [hY] at hy'
          show a ^ 2 * v (t, u) / 3 ≤ bucketOut w x y t u ^ 2
          linarith
  have hv0 : ∀ j, 0 ≤ v j := fun j => retainedMass_nonneg z D x j.1 j.2
  have hvmax : ∀ j, v j ≤ 20 / D := fun j => retainedMass_le z hD x j.1 j.2
  have hV : 7 * (s : ℝ) / 8 ≤ ∑ j, v j := by
    rw [Fintype.sum_prod_type]
    exact retained_total z hz1 D x hx
  have hwb := weighted_bernoulli_lower_tail (fun _ : Fin s × Fin n => uniformLaw Bool) S hS E hE
    (π := 4 / 27) (by norm_num) hπ v hv0 hvmax (by positivity) (κ' := 8 / 81) (by norm_num)
  have hincl : {y | 1 / (s : ℝ) * ∑ t, ∑ u, bucketOut w x y t u ^ 2 < 2 / 81 * a ^ 2} ⊆
      {y | ∑ j, v j * FiniteLaw.indicator (E j) y < 8 / 81 * ∑ j, v j} := by
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    by_contra hcon
    push Not at hcon
    have hpt : ∀ j, a ^ 2 / 3 * (v j * FiniteLaw.indicator (E j) y) ≤
        bucketOut w x y j.1 j.2 ^ 2 := by
      intro j
      by_cases hj : y ∈ E j
      · rw [indicator_of_mem hj, mul_one]
        have hj' : a ^ 2 * v j / 3 ≤ bucketOut w x y j.1 j.2 ^ 2 := hj
        linarith
      · rw [indicator_of_notMem hj, mul_zero, mul_zero]
        positivity
    have hsum : a ^ 2 / 3 * ∑ j, v j * FiniteLaw.indicator (E j) y ≤
        ∑ t, ∑ u, bucketOut w x y t u ^ 2 := by
      rw [Finset.mul_sum, ← Fintype.sum_prod_type']
      exact Finset.sum_le_sum (fun j _ => hpt j)
    have h1 := mul_le_mul_of_nonneg_left hcon (by positivity : (0 : ℝ) ≤ a ^ 2 / 3)
    have h2 := mul_le_mul_of_nonneg_left hV (by positivity : (0 : ℝ) ≤ a ^ 2 / 3 * (8 / 81))
    have h3 : 2 / 81 * a ^ 2 ≤ 1 / (s : ℝ) * ∑ t, ∑ u, bucketOut w x y t u ^ 2 := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hspos]
      nlinarith [mul_nonneg (sq_nonneg a) hspos.le]
    linarith
  have hfinal : Real.exp ((8 / 81 / 2 - 25 / 64 * (4 / 27)) * (∑ j, v j) / (20 / D)) ≤
      Real.exp (-((s : ℝ) * D) / 3200) := by
    apply Real.exp_le_exp.mpr
    have e1 : (8 / 81 / 2 - 25 / 64 * (4 / 27) : ℝ) * (∑ j, v j) / (20 / D) =
        -(11 * (∑ j, v j) * D / 25920) := by
      rw [div_div_eq_mul_div]
      ring
    rw [e1, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hV hD.le, mul_nonneg hspos.le hD.le]
  calc (signLaw s n).prob
        {y | 1 / (s : ℝ) * ∑ t, ∑ u, bucketOut w x y t u ^ 2 < 2 / 81 * a ^ 2}
      ≤ (signLaw s n).prob {y | ∑ j, v j * FiniteLaw.indicator (E j) y < 8 / 81 * ∑ j, v j} :=
        FiniteLaw.prob_mono _ hincl
    _ ≤ Real.exp ((8 / 81 / 2 - 25 / 64 * (4 / 27)) * (∑ j, v j) / (20 / D)) := hwb
    _ ≤ Real.exp (-((s : ℝ) * D) / 3200) := hfinal

end SmallBallAux

end

end SparseStack
