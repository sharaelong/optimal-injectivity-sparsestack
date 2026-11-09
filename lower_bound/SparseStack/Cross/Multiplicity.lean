import SparseStack.Cross.MatrixNorm
import SparseStack.Cross.ProbLemmas

/-!
# Cross-Gram bound, step (4): the multiplicity split `U = U^lo + U^hi` (W-CROSS)

One entry of `U` is `U_{ij} = ∑_t x_{tij}` with `x_{tij}` independent ternary (parameter `b`),
law `rowLaw s b`. With `c = #{t : x_t ≠ 0}`: `U^lo = U 1{c ≤ 2}`, `U^hi = U 1{c ≥ 3}`.

* Symmetry: negating all coordinates (or one coordinate) preserves `rowLaw`.
* `|U^lo| ≤ 2`, `|U^lo| ≤ c`, `E c = s/b` (inputs of the convex order, step (5)).
* `E U^hi = 0`, `E (U^hi)² = E[c 1{c ≥ 3}] ≤ 3 E C(c,3) = 3 C(s,3)/b³`.
* `E ‖U^hi V‖_F² ≤ N d · 3 C(s,3)/b³` (paper, eq. (high-revisit)); the factor `d` comes from
  `∑_j ‖v_j‖² = d`.

Proofs (W-CVX):
* symmetries: a weight-preserving involution preserves expectations (`expect_comp_involutive`);
* `E (U^hi)²`: expand the square; the off-diagonal terms `E[1{c ≥ 3} x_t x_{t'}]` (`t ≠ t'`)
  vanish because flipping the sign of `x_t` preserves the law and `c` and negates the term;
  the diagonal gives `E[1{c ≥ 3} c]`;
* `C(c,3) = ∑_{|T| = 3} ∏_{t ∈ T} 1{x_t ≠ 0}`, so `E C(c,3) = C(s,3) b⁻³` by independence;
* `c 1{c ≥ 3} ≤ 3 C(c,3)` from `3 C(c,3) = c C(c-1,2)`;
* Frobenius: the entries of a row of `U^hi` are independent and centered, so
  `E (U^hi V)_{ik}² = E(U^hi)² ∑_j V_{jk}²`.
-/

namespace SparseStack
namespace Cross

open SparseFock SparseFock.SparseIIDCoupling

/-! ### Helpers -/

/-- A weight-preserving involution preserves expectations. -/
theorem expect_comp_involutive {α : Type*} [Fintype α] (μ : FiniteLaw α) (τ : α → α)
    (hτ : Function.Involutive τ) (hw : ∀ a, μ.weight (τ a) = μ.weight a) (f : α → ℝ) :
    μ.expect (fun a => f (τ a)) = μ.expect f := by
  unfold FiniteLaw.expect
  calc ∑ a, μ.weight a * f (τ a) = ∑ a, μ.weight (τ a) * f (τ a) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hw]
    _ = ∑ a, μ.weight a * f a :=
        Equiv.sum_comp (Function.Involutive.toPerm τ hτ) (fun a => μ.weight a * f a)

theorem mass_negateOutcome (b : ℕ) (z : EtaOutcome) :
    TernaryJacobi.mass b (negateOutcome z) = TernaryJacobi.mass b z := by
  cases z <;> rfl

theorem negateOutcome_ne_zero_iff (z : EtaOutcome) :
    negateOutcome z ≠ EtaOutcome.zero ↔ z ≠ EtaOutcome.zero := by
  cases z <;> simp [negateOutcome]

theorem yValue_mul_self (z : EtaOutcome) :
    yValue z * yValue z = if z ≠ EtaOutcome.zero then 1 else 0 := by
  cases z <;> simp [yValue]

theorem abs_yValue (z : EtaOutcome) :
    |yValue z| = if z ≠ EtaOutcome.zero then 1 else 0 := by
  cases z <;> simp [yValue]

theorem nzCount_cast {s : ℕ} (w : Fin s → EtaOutcome) :
    (nzCount w : ℝ) = ∑ t, (if w t ≠ EtaOutcome.zero then (1 : ℝ) else 0) := by
  unfold nzCount
  exact Finset.natCast_card_filter _ _

theorem nzCount_neg {s : ℕ} (w : Fin s → EtaOutcome) :
    nzCount (fun t => negateOutcome (w t)) = nzCount w := by
  unfold nzCount
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact negateOutcome_ne_zero_iff (w t)

theorem nzCount_flip {s : ℕ} (w : Fin s → EtaOutcome) (t₀ : Fin s) :
    nzCount (Function.update w t₀ (negateOutcome (w t₀))) = nzCount w := by
  unfold nzCount
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases ht : t = t₀
  · subst ht
    rw [Function.update_self]
    exact negateOutcome_ne_zero_iff (w t)
  · rw [Function.update_of_ne ht]

theorem rowSum_neg {s : ℕ} (w : Fin s → EtaOutcome) :
    rowSum (fun t => negateOutcome (w t)) = -rowSum w := by
  unfold rowSum
  simp only [yValue_negateOutcome, Finset.sum_neg_distrib]

/-- `P(x ≠ 0) = 1/b` for one ternary coordinate. -/
theorem expect_coord_nz {b : ℕ} (hb : 0 < b) :
    (coordinateLaw b hb).expect (fun z => if z ≠ EtaOutcome.zero then (1 : ℝ) else 0) =
      1 / (b : ℝ) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [FiniteLaw.expect, coordinateLaw_weight, univ_etaOutcome]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [TernaryJacobi.mass, ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false,
    if_true, if_false, mul_one, mul_zero]
  field_simp
  ring

/-- The squared Frobenius norm is nonnegative. -/
private theorem frobSq_nonneg' {k l : Type} [Fintype k] [Fintype l] (A : Matrix k l ℝ) :
    0 ≤ frobSq A :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))

/-! ### The contracts -/

/-- `U = U^lo + U^hi`. -/
theorem fullMat_eq_loMat_add_hiMat {s n : ℕ} (I : Finset (Fin n))
    (x : Fin n × Fin n → Fin s → EtaOutcome) : fullMat I x = loMat I x + hiMat I x := by
  ext i j
  simp only [fullMat, loMat, hiMat, loPart, hiPart, Matrix.add_apply, Matrix.of_apply]
  split_ifs <;> simp

/-- Negating all coordinates preserves `rowLaw`. -/
theorem expect_rowLaw_neg {s b : ℕ} (hb : 0 < b) (f : (Fin s → EtaOutcome) → ℝ) :
    (rowLaw s b hb).expect (fun w => f (fun t => negateOutcome (w t))) = (rowLaw s b hb).expect f := by
  refine expect_comp_involutive (rowLaw s b hb) (fun w t => negateOutcome (w t)) ?_ ?_ f
  · intro w
    funext t
    exact negateOutcome_involutive (w t)
  · intro w
    show ∏ t, TernaryJacobi.mass b (negateOutcome (w t)) = ∏ t, TernaryJacobi.mass b (w t)
    simp only [mass_negateOutcome]

/-- Negating one coordinate preserves `rowLaw`. -/
theorem expect_rowLaw_flip {s b : ℕ} (hb : 0 < b) (t₀ : Fin s) (f : (Fin s → EtaOutcome) → ℝ) :
    (rowLaw s b hb).expect (fun w => f (Function.update w t₀ (negateOutcome (w t₀)))) =
      (rowLaw s b hb).expect f := by
  refine expect_comp_involutive (rowLaw s b hb)
    (fun w => Function.update w t₀ (negateOutcome (w t₀))) ?_ ?_ f
  · intro w
    funext t
    by_cases ht : t = t₀
    · subst ht
      simp
    · simp only [Function.update_of_ne ht]
  · intro w
    show ∏ t, TernaryJacobi.mass b (Function.update w t₀ (negateOutcome (w t₀)) t) =
      ∏ t, TernaryJacobi.mass b (w t)
    apply Finset.prod_congr rfl
    intro t _
    by_cases ht : t = t₀
    · subst ht
      rw [Function.update_self, mass_negateOutcome]
    · rw [Function.update_of_ne ht]

/-- `E c = s / b`. -/
theorem expect_nzCount {s b : ℕ} (hb : 0 < b) :
    (rowLaw s b hb).expect (fun w => (nzCount w : ℝ)) = s / b := by
  rw [FiniteLaw.expect_congr _ nzCount_cast, expect_sum]
  have h : ∀ t : Fin s, (rowLaw s b hb).expect
      (fun w => if w t ≠ EtaOutcome.zero then (1 : ℝ) else 0) = 1 / (b : ℝ) := by
    intro t
    rw [← expect_coord_nz hb]
    exact FiniteLaw.expect_independentProduct_apply (fun _ : Fin s => coordinateLaw b hb) t
      (fun z => if z ≠ EtaOutcome.zero then (1 : ℝ) else 0)
  rw [Finset.sum_congr rfl (fun t _ => h t), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `|U_{ij}| ≤ c_{ij}`. -/
theorem abs_rowSum_le {s : ℕ} (w : Fin s → EtaOutcome) : |rowSum w| ≤ nzCount w := by
  unfold rowSum
  rw [nzCount_cast]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro t _
  exact abs_yValue (w t)

/-- `|U^lo_{ij}| ≤ 2`. -/
theorem abs_loPart_le_two {s : ℕ} (w : Fin s → EtaOutcome) : |loPart w| ≤ 2 := by
  unfold loPart
  split_ifs with h
  · have h2 : (nzCount w : ℝ) ≤ 2 := by exact_mod_cast h
    exact (abs_rowSum_le w).trans h2
  · simp

/-- `|U^lo_{ij}| ≤ c_{ij}`. -/
theorem abs_loPart_le_nzCount {s : ℕ} (w : Fin s → EtaOutcome) : |loPart w| ≤ nzCount w := by
  unfold loPart
  split_ifs with h
  · exact abs_rowSum_le w
  · simp

/-- `U^lo` is odd under global negation. -/
theorem loPart_neg {s : ℕ} (w : Fin s → EtaOutcome) :
    loPart (fun t => negateOutcome (w t)) = -loPart w := by
  unfold loPart
  rw [nzCount_neg, rowSum_neg]
  split_ifs <;> simp

/-- `U^hi` is odd under global negation. -/
theorem hiPart_neg {s : ℕ} (w : Fin s → EtaOutcome) :
    hiPart (fun t => negateOutcome (w t)) = -hiPart w := by
  unfold hiPart
  rw [nzCount_neg, rowSum_neg]
  split_ifs <;> simp

/-- `E U^hi_{ij} = 0`. -/
theorem expect_hiPart {s b : ℕ} (hb : 0 < b) : (rowLaw s b hb).expect hiPart = 0 := by
  have h := expect_rowLaw_neg (s := s) hb hiPart
  simp only [hiPart_neg, FiniteLaw.expect_neg] at h
  linarith

/-- `E (U^hi)² = E[c 1{c ≥ 3}]` (given the support, the signs are independent). -/
theorem expect_hiPart_sq_eq {s b : ℕ} (hb : 0 < b) :
    (rowLaw s b hb).expect (fun w => hiPart w ^ 2) =
      (rowLaw s b hb).expect (fun w => if nzCount w ≤ 2 then 0 else (nzCount w : ℝ)) := by
  -- `(U^hi)² = ∑_{t,t'} 1{c ≥ 3} x_t x_{t'}`
  have hsq : ∀ w : Fin s → EtaOutcome, hiPart w ^ 2 =
      ∑ t, ∑ t', (if nzCount w ≤ 2 then (0 : ℝ) else 1) * (yValue (w t) * yValue (w t')) := by
    intro w
    by_cases h : nzCount w ≤ 2
    · simp [hiPart, h]
    · simp only [hiPart, rowSum, if_neg h, one_mul]
      rw [sq, Finset.sum_mul_sum]
  -- off-diagonal terms vanish (flip the sign of `x_t`)
  have hoff : ∀ t t' : Fin s, t ≠ t' →
      (rowLaw s b hb).expect
        (fun w => (if nzCount w ≤ 2 then (0 : ℝ) else 1) * (yValue (w t) * yValue (w t'))) =
        0 := by
    intro t t' htt'
    have h := expect_rowLaw_flip hb t
      (fun w => (if nzCount w ≤ 2 then (0 : ℝ) else 1) * (yValue (w t) * yValue (w t')))
    have hflip : ∀ w : Fin s → EtaOutcome,
        (if nzCount (Function.update w t (negateOutcome (w t))) ≤ 2 then (0 : ℝ) else 1) *
          (yValue (Function.update w t (negateOutcome (w t)) t) *
            yValue (Function.update w t (negateOutcome (w t)) t')) =
        -((if nzCount w ≤ 2 then (0 : ℝ) else 1) * (yValue (w t) * yValue (w t'))) := by
      intro w
      rw [nzCount_flip, Function.update_self, Function.update_of_ne htt'.symm,
        yValue_negateOutcome]
      ring
    simp only [hflip, FiniteLaw.expect_neg] at h
    linarith
  -- diagonal: `∑_t 1{c ≥ 3} x_t² = 1{c ≥ 3} c`
  have hdiag : ∀ w : Fin s → EtaOutcome,
      ∑ t, (if nzCount w ≤ 2 then (0 : ℝ) else 1) * (yValue (w t) * yValue (w t)) =
        if nzCount w ≤ 2 then 0 else (nzCount w : ℝ) := by
    intro w
    rw [← Finset.mul_sum]
    simp only [yValue_mul_self]
    rw [← nzCount_cast]
    split_ifs <;> simp
  calc (rowLaw s b hb).expect (fun w => hiPart w ^ 2)
      = (rowLaw s b hb).expect (fun w => ∑ t, ∑ t',
          (if nzCount w ≤ 2 then (0 : ℝ) else 1) * (yValue (w t) * yValue (w t'))) :=
        FiniteLaw.expect_congr _ hsq
    _ = ∑ t, ∑ t', (rowLaw s b hb).expect (fun w =>
          (if nzCount w ≤ 2 then (0 : ℝ) else 1) * (yValue (w t) * yValue (w t'))) := by
        rw [expect_sum]
        apply Finset.sum_congr rfl
        intro t _
        rw [expect_sum]
    _ = ∑ t, (rowLaw s b hb).expect (fun w =>
          (if nzCount w ≤ 2 then (0 : ℝ) else 1) * (yValue (w t) * yValue (w t))) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.sum_eq_single t]
        · intro t' _ ht'
          exact hoff t t' (Ne.symm ht')
        · intro h
          exact absurd (Finset.mem_univ t) h
    _ = (rowLaw s b hb).expect (fun w => ∑ t,
          (if nzCount w ≤ 2 then (0 : ℝ) else 1) * (yValue (w t) * yValue (w t))) :=
        (expect_sum _ _ _).symm
    _ = _ := FiniteLaw.expect_congr _ hdiag

/-- `c 1{c ≥ 3} ≤ 3 C(c,3)`. -/
theorem le_three_mul_choose (c : ℕ) : (if c ≤ 2 then 0 else (c : ℝ)) ≤ 3 * (Nat.choose c 3 : ℝ) := by
  split_ifs with h
  · positivity
  · obtain ⟨k, rfl⟩ : ∃ k, c = k + 3 := ⟨c - 3, by omega⟩
    have h1 : (k + 3) * Nat.choose (k + 2) 2 = Nat.choose (k + 3) 3 * 3 :=
      Nat.add_one_mul_choose_eq (k + 2) 2
    have h2 : 0 < Nat.choose (k + 2) 2 := Nat.choose_pos (by omega)
    have h1R : ((k : ℝ) + 3) * (Nat.choose (k + 2) 2 : ℝ) = (Nat.choose (k + 3) 3 : ℝ) * 3 := by
      exact_mod_cast h1
    have h2R : (1 : ℝ) ≤ (Nat.choose (k + 2) 2 : ℝ) := by
      exact_mod_cast h2
    have h3 := mul_le_mul_of_nonneg_left h2R (by positivity : (0 : ℝ) ≤ (k : ℝ) + 3)
    push_cast
    linarith

/-- `C(c,3)` counts the `3`-subsets of the support. -/
theorem choose_nzCount_cast {s : ℕ} (w : Fin s → EtaOutcome) :
    (Nat.choose (nzCount w) 3 : ℝ) =
      ∑ T ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin s)),
        ∏ t ∈ T, (if w t ≠ EtaOutcome.zero then (1 : ℝ) else 0) := by
  have h1 : Finset.powersetCard 3 (Finset.univ.filter (fun t => w t ≠ EtaOutcome.zero)) =
      (Finset.powersetCard 3 Finset.univ).filter (fun T => ∀ t ∈ T, w t ≠ EtaOutcome.zero) := by
    ext T
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_iff, Finset.mem_univ,
      true_and, implies_true]
    tauto
  unfold nzCount
  rw [← Finset.card_powersetCard, h1, Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.prod_boole]
  by_cases hP : ∀ t ∈ T, w t ≠ EtaOutcome.zero
  · rw [if_pos hP, if_pos hP]
  · rw [if_neg hP, if_neg hP]

/-- `E C(c,3) = C(s,3) b⁻³`. -/
theorem expect_choose_nzCount {s b : ℕ} (hb : 0 < b) :
    (rowLaw s b hb).expect (fun w => (Nat.choose (nzCount w) 3 : ℝ)) =
      (Nat.choose s 3 : ℝ) / (b : ℝ) ^ 3 := by
  rw [FiniteLaw.expect_congr _ choose_nzCount_cast, expect_sum]
  have h : ∀ T ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin s)),
      (rowLaw s b hb).expect
        (fun w => ∏ t ∈ T, (if w t ≠ EtaOutcome.zero then (1 : ℝ) else 0)) = (1 / (b : ℝ)) ^ 3 := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    rw [show rowLaw s b hb = FiniteLaw.independentProduct (fun _ : Fin s => coordinateLaw b hb)
      from rfl]
    rw [FiniteLaw.expect_independentProduct_factorizes_on (fun _ : Fin s => coordinateLaw b hb) T
      (fun _ z => if z ≠ EtaOutcome.zero then (1 : ℝ) else 0)]
    simp only [expect_coord_nz hb, Finset.prod_const, hT.2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `E (U^hi)² ≤ 3 C(s,3) / b³`. -/
theorem expect_hiPart_sq_le {s b : ℕ} (hb : 0 < b) :
    (rowLaw s b hb).expect (fun w => hiPart w ^ 2) ≤ 3 * (Nat.choose s 3 : ℝ) / (b : ℝ) ^ 3 := by
  rw [expect_hiPart_sq_eq hb]
  calc (rowLaw s b hb).expect (fun w => if nzCount w ≤ 2 then 0 else (nzCount w : ℝ))
      ≤ (rowLaw s b hb).expect (fun w => 3 * (Nat.choose (nzCount w) 3 : ℝ)) :=
        FiniteLaw.expect_mono _ (fun w => le_three_mul_choose (nzCount w))
    _ = 3 * (Nat.choose s 3 : ℝ) / (b : ℝ) ^ 3 := by
        rw [FiniteLaw.expect_smul, expect_choose_nzCount hb]
        ring

/-- For an isometry, `∑_j ‖v_j‖² = d`. -/
theorem sum_sq_of_isometry {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ) (hV : V.transpose * V = 1) :
    ∑ j, ∑ k, V j k ^ 2 = (d : ℝ) := by
  have h : ∀ k, ∑ j, V j k ^ 2 = 1 := by
    intro k
    have hk := congrFun (congrFun hV k) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at hk
    calc ∑ j, V j k ^ 2 = ∑ j, V j k * V j k := Finset.sum_congr rfl (fun j _ => sq (V j k))
      _ = 1 := hk
  rw [Finset.sum_comm]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **Step (4)** (paper, eq. (high-revisit)): `E ‖U^hi V‖_F² ≤ N d · 3 C(s,3) / b³`. -/
theorem expect_frobSq_hiMat {s b n d : ℕ} (hb : 0 < b) (I : Finset (Fin n))
    (V : Matrix (Fin n) (Fin d) ℝ) (hV : V.transpose * V = 1) :
    (aggLaw s n b hb).expect (fun x => frobSq (hiMat I x * V)) ≤
      (I.card : ℝ) * d * (3 * (Nat.choose s 3 : ℝ) / (b : ℝ) ^ 3) := by
  have hσ := expect_hiPart_sq_le (s := s) hb
  set σ2 := (rowLaw s b hb).expect (fun w => hiPart w ^ 2) with hσ2
  -- second moments of the entries of one row of `U^hi`
  have hcross : ∀ i j j' : Fin n, (aggLaw s n b hb).expect
      (fun x => hiPart (x (i, j)) * hiPart (x (i, j'))) = if j = j' then σ2 else 0 := by
    intro i j j'
    split_ifs with hjj
    · subst hjj
      rw [hσ2]
      exact (FiniteLaw.expect_independentProduct_apply (fun _ : Fin n × Fin n => rowLaw s b hb)
        (i, j) (fun w => hiPart w * hiPart w)).trans
          (FiniteLaw.expect_congr _ (fun w => (sq (hiPart w)).symm))
    · have hne : (i, j) ≠ (i, j') := fun h => hjj (Prod.mk.inj h).2
      exact (expect_mul_apply_of_ne (fun _ : Fin n × Fin n => rowLaw s b hb) hne hiPart
        hiPart).trans (by rw [expect_hiPart hb, mul_zero])
  -- one entry of `U^hi V`
  have hentry : ∀ (i : Fin n) (k : Fin d), (aggLaw s n b hb).expect
      (fun x => (hiMat I x * V) i k ^ 2) = if i ∈ I then σ2 * ∑ j, V j k ^ 2 else 0 := by
    intro i k
    by_cases hi : i ∈ I
    · rw [if_pos hi]
      have hexp : ∀ x : Fin n × Fin n → Fin s → EtaOutcome, (hiMat I x * V) i k ^ 2 =
          ∑ j, ∑ j', (V j k * V j' k) * (hiPart (x (i, j)) * hiPart (x (i, j'))) := by
        intro x
        simp only [Matrix.mul_apply, hiMat, Matrix.of_apply, if_pos hi]
        rw [sq, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro j' _
        ring
      rw [FiniteLaw.expect_congr _ hexp, expect_sum]
      simp only [expect_sum, FiniteLaw.expect_smul, hcross, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · rw [if_neg hi]
      have hz : ∀ x : Fin n × Fin n → Fin s → EtaOutcome, (hiMat I x * V) i k ^ 2 = 0 := by
        intro x
        simp [Matrix.mul_apply, hiMat, hi]
      rw [FiniteLaw.expect_congr _ hz, FiniteLaw.expect_zero]
  have hrow : ∀ i : Fin n, ∑ k : Fin d, (if i ∈ I then σ2 * ∑ j, V j k ^ 2 else 0) =
      if i ∈ I then σ2 * d else 0 := by
    intro i
    split_ifs
    · rw [← Finset.mul_sum, Finset.sum_comm, sum_sq_of_isometry V hV]
    · simp
  have hfrob : (aggLaw s n b hb).expect (fun x => frobSq (hiMat I x * V)) =
      (I.card : ℝ) * d * σ2 := by
    unfold frobSq
    rw [expect_sum]
    simp only [expect_sum, hentry, hrow]
    rw [Fintype.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hfrob]
  exact mul_le_mul_of_nonneg_left hσ (by positivity)

open scoped Matrix.Norms.L2Operator

/-- Triangle inequality for `U = U^lo + U^hi`. -/
theorem expect_norm_fullMat_le {s b n d : ℕ} (hb : 0 < b) (I : Finset (Fin n))
    (V : Matrix (Fin n) (Fin d) ℝ) :
    (aggLaw s n b hb).expect (fun x => ‖(s : ℝ)⁻¹ • (fullMat I x * V)‖) ≤
      (s : ℝ)⁻¹ * ((aggLaw s n b hb).expect (fun x => ‖loMat I x * V‖) +
        (aggLaw s n b hb).expect (fun x => ‖hiMat I x * V‖)) := by
  rw [← FiniteLaw.expect_add, ← FiniteLaw.expect_smul]
  apply FiniteLaw.expect_mono
  intro x
  rw [norm_smul, Real.norm_of_nonneg (by positivity), fullMat_eq_loMat_add_hiMat, Matrix.add_mul]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)

/-- Operator ≤ Frobenius and Cauchy–Schwarz: `E ‖U^hi V‖ ≤ √(N d · 3 C(s,3) / b³)`. -/
theorem expect_norm_hiMat_le {s b n d : ℕ} (hb : 0 < b) (I : Finset (Fin n))
    (V : Matrix (Fin n) (Fin d) ℝ) (hV : V.transpose * V = 1) :
    (aggLaw s n b hb).expect (fun x => ‖hiMat I x * V‖) ≤
      Real.sqrt ((I.card : ℝ) * d * (3 * (Nat.choose s 3 : ℝ) / (b : ℝ) ^ 3)) := by
  calc (aggLaw s n b hb).expect (fun x => ‖hiMat I x * V‖)
      ≤ (aggLaw s n b hb).expect (fun x => Real.sqrt (frobSq (hiMat I x * V))) :=
        FiniteLaw.expect_mono _ (fun x => l2_opNorm_le_sqrt_frobSq _)
    _ ≤ Real.sqrt ((aggLaw s n b hb).expect
          (fun x => Real.sqrt (frobSq (hiMat I x * V)) ^ 2)) :=
        expect_le_sqrt_expect_sq _ _
    _ = Real.sqrt ((aggLaw s n b hb).expect (fun x => frobSq (hiMat I x * V))) := by
        congr 1
        apply FiniteLaw.expect_congr
        intro x
        exact Real.sq_sqrt (frobSq_nonneg' _)
    _ ≤ _ := Real.sqrt_le_sqrt (expect_frobSq_hiMat hb I V hV)

end Cross
end SparseStack
