import SparseStack.SmallBall.Defs

/-!
# Small ball, hash step: `P{𝓛 > s/16} ≤ e^{-sD/3200}` (paper lines 226–248)

With `p_i = z_i²` (`∑ p_i = 1`, `p_i ≤ 1/D`), bucket masses `W_{tu}` and
`𝓛 = ∑_{t,u} (W_{tu} - 10/D)_+` (`excessMass`):

* `expect_excessMass_le`: `E ∑_u W_{tu}² = ∑_{i,j} p_i p_j P{h_t(i) = h_t(j)} ≤ ∑ p_i² + 1/b ≤ 2/D`
  (`hash_collision`: distinct coordinates collide with probability `1/b`), and
  `(x - A)_+ ≤ x²/(4A)` with `A = 10/D` gives `E 𝓛 ≤ s/20`;
* `excessMass_update`: changing one hash `h_t(i)` moves mass `p_i` from one bucket to another,
  so `𝓛` changes by at most `p_i` (one positive-part increment in `[0, p_i]` is removed, another
  is added);
* `hash_step`: McDiarmid (`mcdiarmid_upper`) on the `s n` hash coordinates with `c_{(t,i)} = p_i`,
  `∑ c² = s ∑ p_i² ≤ s/D`, and `t = s/16 - s/20 = s/80`.
-/

open scoped BigOperators

namespace SparseStack

open SparseFock

noncomputable section

namespace SmallBallAux

/-- `(y - A)_+ ≤ y²/(4A)` for `A > 0`. -/
theorem max_sub_le_sq_div {y A : ℝ} (hA : 0 < A) : max (y - A) 0 ≤ y ^ 2 / (4 * A) := by
  rw [le_div_iff₀ (by positivity)]
  rcases le_total (y - A) 0 with h | h
  · rw [max_eq_right h, zero_mul]
    positivity
  · rw [max_eq_left h]
    nlinarith [sq_nonneg (y - 2 * A)]

/-- `∑_u W_{tu}² = ∑_{i,j} p_i p_j [h_t(i) = h_t(j)]`. -/
theorem sum_sq_bucketMass {s b n : ℕ} (z : Fin n → ℝ) (x : Fin s × Fin n → Fin b)
    (t : Fin s) :
    ∑ u, bucketMass z x t u ^ 2 =
      ∑ i, ∑ j, z i ^ 2 * z j ^ 2 * (if x (t, i) = x (t, j) then 1 else 0) := by
  have key : ∀ i j, ∑ u : Fin b, (if x (t, i) = u then z i ^ 2 else 0) *
      (if x (t, j) = u then z j ^ 2 else 0) =
        z i ^ 2 * z j ^ 2 * (if x (t, i) = x (t, j) then 1 else 0) := by
    intro i j
    rw [Finset.sum_eq_single (x (t, i))]
    · by_cases hij : x (t, i) = x (t, j)
      · rw [if_pos rfl, if_pos hij.symm, if_pos hij, mul_one]
      · rw [if_pos rfl, if_neg (Ne.symm hij), if_neg hij]
        ring
    · intro u _ hu
      rw [if_neg (Ne.symm hu), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  unfold bucketMass
  calc ∑ u, (∑ i, if x (t, i) = u then z i ^ 2 else 0) ^ 2
      = ∑ u, ∑ i, ∑ j, (if x (t, i) = u then z i ^ 2 else 0) *
          (if x (t, j) = u then z j ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, ∑ u, (if x (t, i) = u then z i ^ 2 else 0) *
          (if x (t, j) = u then z j ^ 2 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, z i ^ 2 * z j ^ 2 * (if x (t, i) = x (t, j) then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact key i j

/-- Two distinct hash coordinates collide with probability `1/b`. -/
theorem hash_collision {s b n : ℕ} (hb : 0 < b) {k l : Fin s × Fin n} (hkl : k ≠ l) :
    (hashLaw s b n hb).expect (fun x => if x k = x l then (1 : ℝ) else 0) = 1 / b := by
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hb' : (b : ℝ) ≠ 0 := hbpos.ne'
  have hpt : ∀ x : Fin s × Fin n → Fin b, (if x k = x l then (1 : ℝ) else 0) =
      ∑ u : Fin b, ∏ m ∈ ({k, l} : Finset (Fin s × Fin n)),
        (if x m = u then (1 : ℝ) else 0) := by
    intro x
    rw [Finset.sum_congr rfl (fun u _ => Finset.prod_pair hkl), Finset.sum_eq_single (x k)]
    · by_cases h : x k = x l
      · rw [if_pos h, if_pos rfl, if_pos h.symm, mul_one]
      · rw [if_neg h, if_pos rfl, if_neg (Ne.symm h), mul_zero]
    · intro u _ hu
      rw [if_neg (Ne.symm hu), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hu : ∀ u : Fin b, (hashLaw s b n hb).expect
      (fun x => ∏ m ∈ ({k, l} : Finset (Fin s × Fin n)), (if x m = u then (1 : ℝ) else 0)) =
        1 / (b : ℝ) * (1 / (b : ℝ)) := by
    intro u
    rw [FiniteLaw.expect_independentProduct_factorizes_on _ ({k, l} : Finset (Fin s × Fin n))
      (fun _ a => if a = u then (1 : ℝ) else 0), Finset.prod_pair hkl, uniformLaw_expect]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.card_fin]
  rw [FiniteLaw.expect_congr _ hpt, SparseStack.expect_sum]
  simp only [hu, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- `E 𝓛 ≤ s/20` (paper lines 232–240). -/
theorem expect_excessMass_le {s b n : ℕ} (hb : 0 < b) (z : Fin n → ℝ)
    (hz1 : ∑ i, z i ^ 2 = 1) (D : ℝ) (hD1 : 1 ≤ D) (hDb : D ≤ b)
    (hzinf : ∀ i, z i ^ 2 ≤ 1 / D) :
    (hashLaw s b n hb).expect (excessMass z D) ≤ (s : ℝ) / 20 := by
  have hD : 0 < D := by linarith
  have hD' : D ≠ 0 := hD.ne'
  have hbpos : (0 : ℝ) < b := by linarith
  -- `(W - 10/D)_+ ≤ (D/40) W²`
  have hpt : ∀ x : Fin s × Fin n → Fin b,
      excessMass z D x ≤ ∑ t, D / 40 * ∑ u, bucketMass z x t u ^ 2 := by
    intro x
    unfold excessMass
    apply Finset.sum_le_sum
    intro t _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    have h1 := max_sub_le_sq_div (y := bucketMass z x t u) (A := 10 / D) (by positivity)
    have h2 : bucketMass z x t u ^ 2 / (4 * (10 / D)) = D / 40 * bucketMass z x t u ^ 2 := by
      field_simp
      ring
    linarith
  -- collision bound `P{h_t(i) = h_t(j)} ≤ [i = j] + 1/b`
  have hcoll : ∀ (t : Fin s) (i j : Fin n), (hashLaw s b n hb).expect
      (fun x => if x (t, i) = x (t, j) then (1 : ℝ) else 0) ≤
        (if i = j then 1 else 0) + 1 / b := by
    intro t i j
    by_cases hij : i = j
    · subst hij
      have h1 : (hashLaw s b n hb).expect
          (fun x => if x (t, i) = x (t, i) then (1 : ℝ) else 0) = 1 := by
        simp
      rw [h1, if_pos rfl]
      have : (0 : ℝ) ≤ 1 / b := by positivity
      linarith
    · have hne : ((t, i) : Fin s × Fin n) ≠ (t, j) := by
        intro h
        exact hij (Prod.ext_iff.mp h).2
      rw [hash_collision hb hne, if_neg hij, zero_add]
  -- `E ∑_u W_{tu}² ≤ ∑ p_i² + 1/b ≤ 2/D`
  have hsq : ∀ t, (hashLaw s b n hb).expect (fun x => ∑ u, bucketMass z x t u ^ 2) ≤ 2 / D := by
    intro t
    have e1 : (hashLaw s b n hb).expect (fun x => ∑ u, bucketMass z x t u ^ 2) =
        ∑ i, ∑ j, z i ^ 2 * z j ^ 2 *
          (hashLaw s b n hb).expect (fun x => if x (t, i) = x (t, j) then (1 : ℝ) else 0) := by
      simp only [sum_sq_bucketMass, SparseStack.expect_sum, FiniteLaw.expect_smul]
    have inner : ∀ i, ∑ j, z i ^ 2 * z j ^ 2 * ((if i = j then (1 : ℝ) else 0) + 1 / b) =
        z i ^ 2 * z i ^ 2 + z i ^ 2 / b := by
      intro i
      have h1 : ∀ j, z i ^ 2 * z j ^ 2 * ((if i = j then (1 : ℝ) else 0) + 1 / b) =
          (if i = j then z i ^ 2 * z j ^ 2 else 0) + z i ^ 2 * (z j ^ 2 / b) := by
        intro j
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_add_distrib, Finset.sum_ite_eq,
        if_pos (Finset.mem_univ _), ← Finset.mul_sum, ← Finset.sum_div, hz1]
      ring
    have hp2 : ∑ i, z i ^ 2 * z i ^ 2 ≤ 1 / D := by
      calc ∑ i, z i ^ 2 * z i ^ 2 ≤ ∑ i, z i ^ 2 * (1 / D) :=
            Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hzinf i) (sq_nonneg _))
        _ = 1 / D := by rw [← Finset.sum_mul, hz1, one_mul]
    have hbD : 1 / (b : ℝ) ≤ 1 / D := one_div_le_one_div_of_le hD hDb
    rw [e1]
    calc ∑ i, ∑ j, z i ^ 2 * z j ^ 2 *
          (hashLaw s b n hb).expect (fun x => if x (t, i) = x (t, j) then (1 : ℝ) else 0)
        ≤ ∑ i, ∑ j, z i ^ 2 * z j ^ 2 * ((if i = j then (1 : ℝ) else 0) + 1 / b) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hcoll t i j) (by positivity)
      _ = ∑ i, z i ^ 2 * z i ^ 2 + (∑ i, z i ^ 2) / b := by
          rw [Finset.sum_congr rfl (fun i _ => inner i), Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ 2 / D := by
          rw [hz1]
          have : 2 / D = 1 / D + 1 / D := by ring
          linarith
  calc (hashLaw s b n hb).expect (excessMass z D)
      ≤ (hashLaw s b n hb).expect (fun x => ∑ t, D / 40 * ∑ u, bucketMass z x t u ^ 2) :=
        FiniteLaw.expect_mono _ hpt
    _ = ∑ t, D / 40 * (hashLaw s b n hb).expect (fun x => ∑ u, bucketMass z x t u ^ 2) := by
        rw [SparseStack.expect_sum]
        simp only [FiniteLaw.expect_smul]
    _ ≤ ∑ _t : Fin s, D / 40 * (2 / D) := by
        apply Finset.sum_le_sum
        intro t _
        exact mul_le_mul_of_nonneg_left (hsq t) (by positivity)
    _ = (s : ℝ) / 20 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        ring

/-- Positive-part increment: `0 ≤ (y + p - A)_+ - (y - A)_+ ≤ p` for `p ≥ 0`. -/
theorem max_shift_bounds {y A p : ℝ} (hp : 0 ≤ p) :
    0 ≤ max (y + p - A) 0 - max (y - A) 0 ∧ max (y + p - A) 0 - max (y - A) 0 ≤ p := by
  constructor
  · have : max (y - A) 0 ≤ max (y + p - A) 0 := max_le_max (by linarith) le_rfl
    linarith
  · have : max (y + p - A) 0 ≤ max (y - A) 0 + p := by
      apply max_le
      · linarith [le_max_left (y - A) 0]
      · linarith [le_max_right (y - A) 0]
    linarith

/-- Adding mass `p` to the single bucket `u₀`. -/
theorem sum_max_add_single {b : ℕ} (f : Fin b → ℝ) (A p : ℝ) (u₀ : Fin b) :
    ∑ u, max (f u + (if u₀ = u then p else 0) - A) 0 =
      ∑ u, max (f u - A) 0 + (max (f u₀ + p - A) 0 - max (f u₀ - A) 0) := by
  have h : ∀ u, max (f u + (if u₀ = u then p else 0) - A) 0 =
      max (f u - A) 0 + (if u₀ = u then max (f u + p - A) 0 - max (f u - A) 0 else 0) := by
    intro u
    by_cases hu : u₀ = u
    · simp only [if_pos hu]
      ring
    · simp only [if_neg hu, add_zero]
  rw [Finset.sum_congr rfl (fun u _ => h u), Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

/-- Bounded differences (paper line 241): changing one hash `h_t(i)` changes `𝓛` by at most
`p_i = z_i²`. -/
theorem excessMass_update {s b n : ℕ} (z : Fin n → ℝ) (D : ℝ) (x : Fin s × Fin n → Fin b)
    (k : Fin s × Fin n) (a : Fin b) :
    |excessMass z D (Function.update x k a) - excessMass z D x| ≤ z k.2 ^ 2 := by
  obtain ⟨t, i⟩ := k
  show |excessMass z D (Function.update x (t, i) a) - excessMass z D x| ≤ z i ^ 2
  -- the masses of block `t` are `F u + p_i [h_t(i) = u]`, with `F` independent of `h_t(i)`
  obtain ⟨F, hF⟩ : ∃ F : Fin b → ℝ, ∀ g : Fin s × Fin n → Fin b,
      (∀ j, j ≠ i → g (t, j) = x (t, j)) → ∀ u,
        bucketMass z g t u = F u + (if g (t, i) = u then z i ^ 2 else 0) := by
    refine ⟨fun u => ∑ j, if j = i then 0 else (if x (t, j) = u then z j ^ 2 else 0), ?_⟩
    intro g hg u
    have hsplit : ∀ j, (if g (t, j) = u then z j ^ 2 else 0) =
        (if j = i then 0 else (if x (t, j) = u then z j ^ 2 else 0)) +
          (if j = i then (if g (t, i) = u then z i ^ 2 else 0) else 0) := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [if_neg hj, if_neg hj, add_zero, hg j hj]
    unfold bucketMass
    rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
  have hne : ∀ t' j, (t', j) ≠ (t, i) → Function.update x (t, i) a (t', j) = x (t', j) :=
    fun t' j h => Function.update_of_ne h a x
  have hW' : ∀ u, bucketMass z (Function.update x (t, i) a) t u =
      F u + (if a = u then z i ^ 2 else 0) := by
    intro u
    rw [hF (Function.update x (t, i) a)
      (fun j hj => hne t j (fun h => hj (Prod.ext_iff.mp h).2)) u, Function.update_self]
  have hWx : ∀ u, bucketMass z x t u = F u + (if x (t, i) = u then z i ^ 2 else 0) :=
    hF x (fun j _ => rfl)
  have hother : ∀ t', t' ≠ t → ∀ u,
      bucketMass z (Function.update x (t, i) a) t' u = bucketMass z x t' u := by
    intro t' ht' u
    unfold bucketMass
    apply Finset.sum_congr rfl
    intro j _
    rw [hne t' j (fun h => ht' (Prod.ext_iff.mp h).1)]
  have hdiff : excessMass z D (Function.update x (t, i) a) - excessMass z D x =
      ∑ u, max (bucketMass z (Function.update x (t, i) a) t u - 10 / D) 0 -
        ∑ u, max (bucketMass z x t u - 10 / D) 0 := by
    unfold excessMass
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single t]
    · intro t' _ ht'
      rw [sub_eq_zero]
      apply Finset.sum_congr rfl
      intro u _
      rw [hother t' ht' u]
    · intro h
      exact absurd (Finset.mem_univ t) h
  rw [hdiff]
  simp only [hW', hWx]
  rw [sum_max_add_single F (10 / D) (z i ^ 2) a,
    sum_max_add_single F (10 / D) (z i ^ 2) (x (t, i))]
  obtain ⟨h1, h2⟩ := max_shift_bounds (y := F a) (A := 10 / D) (sq_nonneg (z i))
  obtain ⟨h3, h4⟩ := max_shift_bounds (y := F (x (t, i))) (A := 10 / D) (sq_nonneg (z i))
  rw [abs_le]
  constructor <;> linarith

/-- Hash step (paper lines 241–248): `P{𝓛 > s/16} ≤ e^{-sD/3200}`. -/
theorem hash_step {s b n : ℕ} (hs : 0 < s) (hb : 0 < b) (z : Fin n → ℝ)
    (hz1 : ∑ i, z i ^ 2 = 1) (D : ℝ) (hD1 : 1 ≤ D) (hDb : D ≤ b)
    (hzinf : ∀ i, z i ^ 2 ≤ 1 / D) :
    (hashLaw s b n hb).prob {x | (s : ℝ) / 16 < excessMass z D x} ≤
      Real.exp (-((s : ℝ) * D) / 3200) := by
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  have hD : 0 < D := by linarith
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hE := expect_excessMass_le (s := s) hb z hz1 D hD1 hDb hzinf
  have hmc := mcdiarmid_upper (fun _ : Fin s × Fin n => uniformLaw (Fin b)) (excessMass z D)
    (fun k => z k.2 ^ 2) (fun x k a => excessMass_update z D x k a)
    (t := (s : ℝ) / 80) (by positivity)
  have hC : ∑ k : Fin s × Fin n, (z k.2 ^ 2) ^ 2 = (s : ℝ) * ∑ i, (z i ^ 2) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hC4 : ∑ i, (z i ^ 2) ^ 2 ≤ 1 / D := by
    calc ∑ i, (z i ^ 2) ^ 2 ≤ ∑ i, z i ^ 2 * (1 / D) := by
          apply Finset.sum_le_sum
          intro i _
          rw [sq (z i ^ 2)]
          exact mul_le_mul_of_nonneg_left (hzinf i) (sq_nonneg _)
      _ = 1 / D := by rw [← Finset.sum_mul, hz1, one_mul]
  have hC4pos : 0 < ∑ i, (z i ^ 2) ^ 2 := by
    by_contra hneg
    push Not at hneg
    have h0 : ∑ i, (z i ^ 2) ^ 2 = 0 :=
      le_antisymm hneg (Finset.sum_nonneg (fun i _ => by positivity))
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)] at h0
    have : ∑ i, z i ^ 2 = 0 :=
      Finset.sum_eq_zero (fun i hi => (pow_eq_zero_iff two_ne_zero).mp (h0 i hi))
    linarith
  have hDS : D * ∑ i, (z i ^ 2) ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hC4 hD.le
    rwa [mul_one_div_cancel hD.ne'] at this
  calc (hashLaw s b n hb).prob {x | (s : ℝ) / 16 < excessMass z D x}
      ≤ (hashLaw s b n hb).prob
          {x | (hashLaw s b n hb).expect (excessMass z D) + (s : ℝ) / 80 ≤
            excessMass z D x} := by
        apply FiniteLaw.prob_mono
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        linarith
    _ ≤ Real.exp (-2 * ((s : ℝ) / 80) ^ 2 / ∑ k : Fin s × Fin n, (z k.2 ^ 2) ^ 2) := hmc
    _ ≤ Real.exp (-((s : ℝ) * D) / 3200) := by
        apply Real.exp_le_exp.mpr
        rw [hC]
        have key : (s : ℝ) * D / 3200 ≤
            2 * ((s : ℝ) / 80) ^ 2 / ((s : ℝ) * ∑ i, (z i ^ 2) ^ 2) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hDS (by positivity : (0 : ℝ) ≤ (s : ℝ) * s)]
        have e : -2 * ((s : ℝ) / 80) ^ 2 / ((s : ℝ) * ∑ i, (z i ^ 2) ^ 2) =
            -(2 * ((s : ℝ) / 80) ^ 2 / ((s : ℝ) * ∑ i, (z i ^ 2) ^ 2)) := by ring
        rw [e, neg_div]
        exact neg_le_neg key

end SmallBallAux

end

end SparseStack
