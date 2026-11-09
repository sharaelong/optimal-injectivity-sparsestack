import SparseFockFormal.FiniteProbability
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen

/-!
# Finite-law helpers for the Heidary bridges (W-HEID)

* `expect_finset_sum`: linearity of `FiniteLaw.expect` over finite sums;
* `pow_expect_le_expect_pow`: Jensen `(E f)^k ≤ E f^k` for `f ≥ 0`;
* `expect_le_of_expect_pow_le`: Lyapunov form `E f ≤ K` from `E f^k ≤ K^k`;
* `expect_independentProduct_curry`: an independent product over sites `ι × κ` is the
  independent product over `ι` of the independent products over `κ` (regrouping by rows).
-/

namespace SparseStack.HeidBridge

open SparseFock

/-- Linearity of the expectation over a finite sum. -/
theorem expect_finset_sum {α ι : Type*} [Fintype α] (μ : FiniteLaw α) (s : Finset ι)
    (f : ι → α → ℝ) :
    μ.expect (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, μ.expect (f i) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_comm

/-- Jensen's inequality for the convex power `t ↦ t^k` on `[0, ∞)`: `(E f)^k ≤ E f^k`. -/
theorem pow_expect_le_expect_pow {α : Type*} [Fintype α] (μ : FiniteLaw α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (k : ℕ) : μ.expect f ^ k ≤ μ.expect (fun x => f x ^ k) := by
  have h := (convexOn_pow (𝕜 := ℝ) k).map_sum_le (t := Finset.univ) (w := μ.weight) (p := f)
    (fun x _ => μ.weight_nonneg x) μ.sum_weight (fun x _ => Set.mem_Ici.mpr (hf x))
  simpa only [FiniteLaw.expect, smul_eq_mul] using h

/-- Lyapunov: a `k`-th moment bound `E f^k ≤ K^k` gives `E f ≤ K` (for `f ≥ 0`, `K ≥ 0`). -/
theorem expect_le_of_expect_pow_le {α : Type*} [Fintype α] (μ : FiniteLaw α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) {k : ℕ} (hk : k ≠ 0) {K : ℝ} (hK : 0 ≤ K)
    (h : μ.expect (fun x => f x ^ k) ≤ K ^ k) : μ.expect f ≤ K := by
  have h1 := (pow_expect_le_expect_pow μ f hf k).trans h
  exact (pow_le_pow_iff_left₀ (μ.expect_nonneg hf) hK hk).1 h1

/-- Regrouping an independent product over sites `ι × κ` by rows `i : ι`. -/
theorem expect_independentProduct_curry {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype α] (μ : ι × κ → FiniteLaw α)
    (f : (ι × κ → α) → ℝ) :
    (FiniteLaw.independentProduct μ).expect f =
      (FiniteLaw.independentProduct (fun i => FiniteLaw.independentProduct
        (fun k => μ (i, k)))).expect (fun y => f (fun p => y p.1 p.2)) := by
  simp only [FiniteLaw.expect, FiniteLaw.independentProduct_weight]
  refine Fintype.sum_equiv (Equiv.curry ι κ α) _ _ ?_
  intro x
  rw [Fintype.prod_prod_type]
  rfl

end SparseStack.HeidBridge
