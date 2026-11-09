import SparseStack.Cross.Defs

/-!
# Cross-Gram bound: finite-probability helpers (W-CROSS)

Generic lemmas on Heidary's finite laws used by the cross-Gram proof.

* `expect_le_sqrt_expect_sq`: Cauchy–Schwarz `E f ≤ √(E f²)` (step (7)).
* `expect_comm`: Fubini for two finite laws.
* `expect_resample_one`: resampling one coordinate of an independent product (hybrid argument of
  step (5)).
* `expect_mul_apply_of_ne`: two distinct coordinates are independent (step (4)).
* `expect_prod_comp_injOn`: factorization of a product of coordinates selected by an injective map.
* `expect_select`, `expect_nested_eq_flat`, `expect_select_nested`: the *selection identity*
  (coordinates selected injectively from an iid family and sign-adjusted, completed by fresh
  coordinates, again form an iid family) — the distributional identity of step (3), and the row
  padding of step (6).
* `expect_mixture`: if `∑ₓ μ(x) cond(x)(y) = ν(y)`, then drawing `x ~ μ^κ` and then `y ~ ∏ cond(x_k)`
  gives `y ~ ν^κ` (selector coupling, step (2)).
-/

namespace SparseStack
namespace Cross

open SparseFock

/-- Linearity of the expectation for a finite linear combination. -/
theorem expect_sum_mul {α ι : Type*} [Fintype α] (μ : FiniteLaw α) (s : Finset ι) (c : ι → ℝ)
    (f : ι → α → ℝ) :
    μ.expect (fun x => ∑ i ∈ s, c i * f i x) = ∑ i ∈ s, c i * μ.expect (f i) := by
  rw [expect_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact FiniteLaw.expect_smul μ (c i) (f i)

/-- The expectation of the indicator of a point is its weight. -/
theorem expect_ite_eq {α : Type*} [Fintype α] [DecidableEq α] (μ : FiniteLaw α) (c : α) :
    μ.expect (fun a => if a = c then (1 : ℝ) else 0) = μ.weight c := by
  simp [FiniteLaw.expect]

/-- Cauchy–Schwarz for a finite law: `E f ≤ √(E f²)`. -/
theorem expect_le_sqrt_expect_sq {α : Type*} [Fintype α] (μ : FiniteLaw α) (f : α → ℝ) :
    μ.expect f ≤ Real.sqrt (μ.expect (fun x => f x ^ 2)) := by
  have hvar : 0 ≤ μ.expect (fun x => (f x - μ.expect f) ^ 2) :=
    μ.expect_nonneg (fun x => sq_nonneg _)
  have hexp : μ.expect (fun x => (f x - μ.expect f) ^ 2) =
      μ.expect (fun x => f x ^ 2) - (μ.expect f) ^ 2 := by
    have hpt : ∀ x, (f x - μ.expect f) ^ 2 =
        (f x ^ 2 + (-2 * μ.expect f) * f x) + (μ.expect f) ^ 2 := fun x => by ring
    rw [μ.expect_congr hpt, FiniteLaw.expect_add, FiniteLaw.expect_add, FiniteLaw.expect_smul,
      FiniteLaw.expect_const]
    ring
  have hsq : (μ.expect f) ^ 2 ≤ μ.expect (fun x => f x ^ 2) := by linarith
  calc μ.expect f ≤ |μ.expect f| := le_abs_self _
    _ = Real.sqrt ((μ.expect f) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (μ.expect (fun x => f x ^ 2)) := Real.sqrt_le_sqrt hsq

/-- Fubini for two finite laws. -/
theorem expect_comm {α β : Type*} [Fintype α] [Fintype β] (μ : FiniteLaw α) (ν : FiniteLaw β)
    (f : α → β → ℝ) :
    μ.expect (fun x => ν.expect (fun y => f x y)) = ν.expect (fun y => μ.expect (fun x => f x y)) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Resampling one coordinate of an independent product. -/
theorem expect_resample_one {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (μ : ι → FiniteLaw α) (e : ι) (G : (ι → α) → ℝ) :
    (FiniteLaw.independentProduct μ).expect G =
      (FiniteLaw.independentProduct μ).expect
        (fun x => (μ e).expect (fun a => G (Function.update x e a))) := by
  rw [← expect_expect_piecewise μ {e} G]
  apply FiniteLaw.expect_congr
  intro y
  simp only [Finset.piecewise_singleton]
  exact FiniteLaw.expect_independentProduct_apply μ e (fun a => G (Function.update y e a))

/-- Two distinct coordinates of an independent product are independent. -/
theorem expect_mul_apply_of_ne {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (μ : ι → FiniteLaw α) {e e' : ι} (he : e ≠ e') (f g : α → ℝ) :
    (FiniteLaw.independentProduct μ).expect (fun x => f (x e) * g (x e')) =
      (μ e).expect f * (μ e').expect g := by
  rw [expect_mul_of_dependsOn μ {e} (fun x => f (x e)) (fun x => g (x e')) ?_ ?_,
    FiniteLaw.expect_independentProduct_apply, FiniteLaw.expect_independentProduct_apply]
  · intro x y hxy
    rw [hxy e (Finset.mem_singleton_self e)]
  · intro x y hxy
    rw [hxy e' (by rw [Finset.mem_singleton]; exact he.symm)]

/-- Factorization of a product of coordinates selected by a map that is injective on the index
set. -/
theorem expect_prod_comp_injOn {K E α : Type*} [Fintype K] [DecidableEq K] [Fintype α]
    [DecidableEq E] (μ : K → FiniteLaw α) (S : Finset E) (φ : E → K) (hφ : Set.InjOn φ S)
    (f : E → α → ℝ) :
    (FiniteLaw.independentProduct μ).expect (fun y => ∏ e ∈ S, f e (y (φ e))) =
      ∏ e ∈ S, (μ (φ e)).expect (f e) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hφS : Set.InjOn φ S := hφ.mono (by
      intro x hx
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx)))
    simp only [Finset.prod_insert ha]
    rw [expect_mul_of_dependsOn μ {φ a} (fun y => f a (y (φ a)))
        (fun y => ∏ e ∈ S, f e (y (φ e))) ?_ ?_, ih hφS,
      FiniteLaw.expect_independentProduct_apply]
    · intro x y hxy
      rw [hxy (φ a) (Finset.mem_singleton_self _)]
    · intro x y hxy
      apply Finset.prod_congr rfl
      intro e he
      rw [hxy (φ e) ?_]
      rw [Finset.mem_singleton]
      intro hea
      have hea' : e = a := hφ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem he))
        (Finset.mem_coe.mpr (Finset.mem_insert_self a S)) hea
      exact ha (hea' ▸ he)

/-- **Selection identity.** Select the coordinates `sel e` of an iid family `x` from an independent
iid family `y` along a map `φ` that is injective on the selected set, apply measure-preserving
involutions `τ e`, and keep the other coordinates of `x`: the result is again iid. -/
theorem expect_select {K E α : Type*} [Fintype K] [DecidableEq K] [Fintype E] [DecidableEq E]
    [Fintype α] [DecidableEq α] (μ : FiniteLaw α) (sel : E → Prop) [DecidablePred sel]
    (φ : E → K) (hφ : ∀ e e', sel e → sel e' → φ e = φ e' → e = e')
    (τ : E → α → α) (hτinv : ∀ e a, τ e (τ e a) = a) (hτ : ∀ e a, μ.weight (τ e a) = μ.weight a)
    (F : (E → α) → ℝ) :
    (FiniteLaw.independentProduct (fun _ : K => μ)).expect (fun y =>
      (FiniteLaw.independentProduct (fun _ : E => μ)).expect (fun x' =>
        F (fun e => if sel e then τ e (y (φ e)) else x' e))) =
      (FiniteLaw.independentProduct (fun _ : E => μ)).expect F := by
  set P := FiniteLaw.independentProduct (fun _ : K => μ) with hP
  set Q := FiniteLaw.independentProduct (fun _ : E => μ) with hQ
  -- point-mass expansion of `F`
  have hdecomp : ∀ x : E → α, F x = ∑ z, F z * ∏ e, (if x e = z e then (1 : ℝ) else 0) := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp
    · intro z _ hzx
      obtain ⟨e, he⟩ : ∃ e, x e ≠ z e := by
        by_contra h
        push Not at h
        exact hzx (funext h).symm
      rw [Finset.prod_eq_zero (Finset.mem_univ e) (if_neg he), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ x) h
  -- the point indicator splits into a selected and a fresh part
  have hsplit : ∀ (z : E → α) (y : K → α) (x' : E → α),
      (∏ e, (if (if sel e then τ e (y (φ e)) else x' e) = z e then (1 : ℝ) else 0)) =
        (∏ e ∈ Finset.univ.filter sel, (if y (φ e) = τ e (z e) then (1 : ℝ) else 0)) *
          ∏ e, (if sel e then (1 : ℝ) else (if x' e = z e then (1 : ℝ) else 0)) := by
    intro z y x'
    rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e _
    by_cases hs : sel e
    · have hiff : (τ e (y (φ e)) = z e) ↔ (y (φ e) = τ e (z e)) := by
        constructor
        · intro h
          rw [← h, hτinv]
        · intro h
          rw [h, hτinv]
      simp only [if_pos hs, mul_one]
      by_cases h1 : y (φ e) = τ e (z e)
      · rw [if_pos (hiff.mpr h1), if_pos h1]
      · rw [if_neg (fun h => h1 (hiff.mp h)), if_neg h1]
    · simp only [if_neg hs, one_mul]
  -- probability of a point
  have hprob : ∀ z : E → α,
      P.expect (fun y => Q.expect (fun x' =>
        ∏ e, (if (if sel e then τ e (y (φ e)) else x' e) = z e then (1 : ℝ) else 0))) =
        Q.weight z := by
    intro z
    simp only [hsplit z]
    have hQB : Q.expect (fun x' =>
        ∏ e, (if sel e then (1 : ℝ) else (if x' e = z e then (1 : ℝ) else 0))) =
        ∏ e, (if sel e then (1 : ℝ) else μ.weight (z e)) := by
      rw [hQ, FiniteLaw.expect_independentProduct_factorizes (fun _ : E => μ)
        (fun e a => if sel e then (1 : ℝ) else (if a = z e then (1 : ℝ) else 0))]
      apply Finset.prod_congr rfl
      intro e _
      by_cases hs : sel e
      · simp only [if_pos hs, FiniteLaw.expect_const]
      · simp only [if_neg hs]
        exact expect_ite_eq μ (z e)
    have hPA : P.expect (fun y =>
        ∏ e ∈ Finset.univ.filter sel, (if y (φ e) = τ e (z e) then (1 : ℝ) else 0)) =
        ∏ e ∈ Finset.univ.filter sel, μ.weight (z e) := by
      rw [hP, expect_prod_comp_injOn (fun _ : K => μ) (Finset.univ.filter sel) φ ?_
        (fun e a => if a = τ e (z e) then (1 : ℝ) else 0)]
      · apply Finset.prod_congr rfl
        intro e _
        rw [expect_ite_eq, hτ]
      · intro e he e' he' hee'
        exact hφ e e' (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
          (Finset.mem_filter.mp (Finset.mem_coe.mp he')).2 hee'
    calc P.expect (fun y => Q.expect (fun x' =>
          (∏ e ∈ Finset.univ.filter sel, (if y (φ e) = τ e (z e) then (1 : ℝ) else 0)) *
            ∏ e, (if sel e then (1 : ℝ) else (if x' e = z e then (1 : ℝ) else 0))))
        = P.expect (fun y =>
            (∏ e ∈ Finset.univ.filter sel, (if y (φ e) = τ e (z e) then (1 : ℝ) else 0)) *
              ∏ e, (if sel e then (1 : ℝ) else μ.weight (z e))) := by
          apply FiniteLaw.expect_congr
          intro y
          rw [FiniteLaw.expect_smul, hQB]
      _ = (∏ e ∈ Finset.univ.filter sel, μ.weight (z e)) *
            ∏ e, (if sel e then (1 : ℝ) else μ.weight (z e)) := by
          rw [expect_mul_const, hPA]
      _ = Q.weight z := by
          rw [hQ, FiniteLaw.independentProduct_weight, Finset.prod_filter,
            ← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro e _
          by_cases hs : sel e
          · simp only [if_pos hs, mul_one]
          · simp only [if_neg hs, one_mul]
  -- assemble
  calc P.expect (fun y => Q.expect (fun x' => F (fun e => if sel e then τ e (y (φ e)) else x' e)))
      = P.expect (fun y => Q.expect (fun x' => ∑ z, F z *
          ∏ e, (if (if sel e then τ e (y (φ e)) else x' e) = z e then (1 : ℝ) else 0))) := by
        apply FiniteLaw.expect_congr
        intro y
        apply FiniteLaw.expect_congr
        intro x'
        exact hdecomp _
    _ = P.expect (fun y => ∑ z, F z * Q.expect (fun x' =>
          ∏ e, (if (if sel e then τ e (y (φ e)) else x' e) = z e then (1 : ℝ) else 0))) := by
        apply FiniteLaw.expect_congr
        intro y
        exact expect_sum_mul Q Finset.univ F _
    _ = ∑ z, F z * P.expect (fun y => Q.expect (fun x' =>
          ∏ e, (if (if sel e then τ e (y (φ e)) else x' e) = z e then (1 : ℝ) else 0))) :=
        expect_sum_mul P Finset.univ F _
    _ = ∑ z, F z * Q.weight z := by
        apply Finset.sum_congr rfl
        intro z _
        rw [hprob z]
    _ = Q.expect F := by
        rw [FiniteLaw.expect]
        apply Finset.sum_congr rfl
        intro z _
        ring

/-- A nested iid product is the flat iid product on the product index. -/
theorem expect_nested_eq_flat {K₁ K₂ α : Type*} [Fintype K₁] [DecidableEq K₁] [Fintype K₂]
    [DecidableEq K₂] [Fintype α] (μ : FiniteLaw α) (F : (K₁ → K₂ → α) → ℝ) :
    (FiniteLaw.independentProduct
        (fun _ : K₁ => FiniteLaw.independentProduct (fun _ : K₂ => μ))).expect F =
      (FiniteLaw.independentProduct (fun _ : K₁ × K₂ => μ)).expect
        (fun x => F (fun a c => x (a, c))) := by
  simp only [FiniteLaw.expect, FiniteLaw.independentProduct_weight]
  rw [← (Equiv.curry K₁ K₂ α).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_prod_type]
  rfl

/-- The selection identity for nested iid products. -/
theorem expect_select_nested {K₁ K₂ E₁ E₂ α : Type*} [Fintype K₁] [DecidableEq K₁] [Fintype K₂]
    [DecidableEq K₂] [Fintype E₁] [DecidableEq E₁] [Fintype E₂] [DecidableEq E₂] [Fintype α]
    [DecidableEq α] (μ : FiniteLaw α) (sel : E₁ → E₂ → Prop) [∀ e₁ e₂, Decidable (sel e₁ e₂)]
    (φ₁ : E₁ → E₂ → K₁) (φ₂ : E₁ → E₂ → K₂)
    (hφ : ∀ e₁ e₂ e₁' e₂', sel e₁ e₂ → sel e₁' e₂' → φ₁ e₁ e₂ = φ₁ e₁' e₂' →
      φ₂ e₁ e₂ = φ₂ e₁' e₂' → e₁ = e₁' ∧ e₂ = e₂')
    (τ : E₁ → E₂ → α → α) (hτinv : ∀ e₁ e₂ a, τ e₁ e₂ (τ e₁ e₂ a) = a)
    (hτ : ∀ e₁ e₂ a, μ.weight (τ e₁ e₂ a) = μ.weight a) (F : (E₁ → E₂ → α) → ℝ) :
    (FiniteLaw.independentProduct
        (fun _ : K₁ => FiniteLaw.independentProduct (fun _ : K₂ => μ))).expect (fun y =>
      (FiniteLaw.independentProduct
          (fun _ : E₁ => FiniteLaw.independentProduct (fun _ : E₂ => μ))).expect (fun x' =>
        F (fun e₁ e₂ => if sel e₁ e₂ then τ e₁ e₂ (y (φ₁ e₁ e₂) (φ₂ e₁ e₂)) else x' e₁ e₂))) =
      (FiniteLaw.independentProduct
          (fun _ : E₁ => FiniteLaw.independentProduct (fun _ : E₂ => μ))).expect F := by
  simp only [expect_nested_eq_flat μ]
  exact expect_select μ (fun p : E₁ × E₂ => sel p.1 p.2) (fun p => (φ₁ p.1 p.2, φ₂ p.1 p.2))
    (fun p p' hp hp' h => by
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      obtain ⟨e1, e2⟩ := hφ p.1 p.2 p'.1 p'.2 hp hp' h1 h2
      exact Prod.ext e1 e2)
    (fun p => τ p.1 p.2) (fun p a => hτinv p.1 p.2 a) (fun p a => hτ p.1 p.2 a)
    (fun x => F (fun a c => x (a, c)))

/-- **Mixture identity.** If `∑ₓ μ(x) cond(x)(y) = ν(y)`, drawing `x ~ μ^κ` and then
`y ~ ∏ₖ cond(x k)` gives `y ~ ν^κ`. -/
theorem expect_mixture {κ X Y : Type*} [Fintype κ] [DecidableEq κ] [Fintype X] [Fintype Y]
    (μ : FiniteLaw X) (ν : FiniteLaw Y) (cond : X → FiniteLaw Y)
    (hmarg : ∀ y, ∑ x, μ.weight x * (cond x).weight y = ν.weight y) (f : (κ → Y) → ℝ) :
    (FiniteLaw.independentProduct (fun _ : κ => μ)).expect (fun x =>
      (FiniteLaw.independentProduct (fun k => cond (x k))).expect f) =
      (FiniteLaw.independentProduct (fun _ : κ => ν)).expect f := by
  simp only [FiniteLaw.expect, FiniteLaw.independentProduct_weight, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have hpt : ∀ x : κ → X, (∏ k, μ.weight (x k)) * ((∏ k, (cond (x k)).weight (y k)) * f y) =
      (∏ k, μ.weight (x k) * (cond (x k)).weight (y k)) * f y := by
    intro x
    rw [Finset.prod_mul_distrib]
    ring
  simp only [hpt]
  rw [← Finset.sum_mul, ← Fintype.prod_sum (fun k a => μ.weight a * (cond a).weight (y k))]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact hmarg (y k)

end Cross
end SparseStack
