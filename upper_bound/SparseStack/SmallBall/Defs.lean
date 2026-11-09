import SparseStack.Prob.Sketch
import SparseStack.SmallBall.Rademacher

/-!
# Small ball: sample-space split and bucket quantities (helper for `lem:smallball`)

* The uniform sketch law is the product of the hash law `hashLaw` (independent uniform hashes
  indexed by pairs `(t, i)`) and the sign law `signLaw` (independent uniform bits indexed by
  `(t, i)`): `sketchLaw_prob_eq` (Fubini over the split `ω = toSample x y`).
* `bucketOut w x y t u = ∑_{i : x(t,i) = u} σ_{ti} w_i` is the unnormalized output of bucket
  `(t, u)`, and `‖Π w‖² = (1/s) ∑_{t,u} bucketOut² ` (`sqNorm_sketch_eq`).
* Paper notation (lines 226–254): `p_i = z_i²`, bucket masses `W_{tu} = bucketMass`, the excess
  `𝓛 = excessMass = ∑_{t,u} (W_{tu} - 10/D)_+`, and the retained masses
  `retainedMass = W_{tu} · [W_{tu} ≤ 20/D]`.
-/

open scoped BigOperators

namespace SparseStack

open SparseFock

noncomputable section

namespace SmallBallAux

/-- The hashes, indexed by pairs `(t, i)`: independent and uniform on `Fin b`. -/
abbrev hashLaw (s b n : ℕ) (hb : 0 < b) : FiniteLaw (Fin s × Fin n → Fin b) :=
  FiniteLaw.independentProduct (fun _ : Fin s × Fin n => @uniformLaw (Fin b) _ ⟨⟨0, hb⟩⟩)

/-- The signs, indexed by pairs `(t, i)`: independent uniform bits. -/
abbrev signLaw (s n : ℕ) : FiniteLaw (Fin s × Fin n → Bool) := signsLaw (Fin s × Fin n)

/-- The sketch sample point with hashes `x` and signs `y`. -/
def toSample {s b n : ℕ} (x : Fin s × Fin n → Fin b) (y : Fin s × Fin n → Bool) :
    SketchSample s b n :=
  (fun t i => x (t, i), fun t i => y (t, i))

/-- Uniform laws are invariant under equivalences. -/
theorem uniformLaw_prob_equiv {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (E : Set β) : (uniformLaw β).prob E = (uniformLaw α).prob {x | e x ∈ E} := by
  unfold FiniteLaw.prob
  rw [uniformLaw_expect, uniformLaw_expect, Fintype.card_congr e]
  congr 1
  exact (Equiv.sum_comp e (FiniteLaw.indicator E)).symm

/-- The uniform sketch law splits into hashes and signs (Fubini). -/
theorem sketchLaw_prob_eq {s b n : ℕ} (hb : 0 < b) (E : Set (SketchSample s b n)) :
    (sketchLaw s b n hb).prob E =
      (hashLaw s b n hb).expect (fun x => (signLaw s n).prob {y | toSample x y ∈ E}) := by
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  have h1 : sketchLaw s b n hb = uniformLaw (SketchSample s b n) :=
    finiteLaw_ext (fun _ => rfl)
  have h2 : hashLaw s b n hb = uniformLaw (Fin s × Fin n → Fin b) :=
    independentProduct_uniformLaw _ _
  have h3 : signLaw s n = uniformLaw (Fin s × Fin n → Bool) :=
    independentProduct_uniformLaw _ _
  rw [h1, h2, h3, uniformLaw_prob_equiv
    (Equiv.prodCongr (Equiv.curry (Fin s) (Fin n) (Fin b)) (Equiv.curry (Fin s) (Fin n) Bool)) E,
    ← prodLaw_uniformLaw, prob_prodLaw]
  rfl

/-- Unnormalized output of bucket `(t, u)`: `∑_{i : h_t(i) = u} σ_{ti} w_i`. -/
def bucketOut {s b n : ℕ} (w : Fin n → ℝ) (x : Fin s × Fin n → Fin b)
    (y : Fin s × Fin n → Bool) (t : Fin s) (u : Fin b) : ℝ :=
  ∑ i, if x (t, i) = u then signValue (y (t, i)) * w i else 0

/-- `‖Π w‖² = (1/s) ∑_{t,u} (∑_{i : h_t(i) = u} σ_{ti} w_i)²`. -/
theorem sqNorm_sketch_eq {s b n : ℕ} (w : Fin n → ℝ) (x : Fin s × Fin n → Fin b)
    (y : Fin s × Fin n → Bool) :
    sqNorm ((sketchMatrix (toSample x y)).mulVec w) =
      1 / (s : ℝ) * ∑ t, ∑ u, bucketOut w x y t u ^ 2 := by
  have hentry : ∀ (t : Fin s) (u : Fin b) (i : Fin n), sketchMatrix (toSample x y) (t, u) i =
      (Real.sqrt s)⁻¹ * (if x (t, i) = u then signValue (y (t, i)) else 0) :=
    fun _ _ _ => rfl
  have hmv : ∀ (t : Fin s) (u : Fin b), (sketchMatrix (toSample x y)).mulVec w (t, u) =
      (Real.sqrt s)⁻¹ * bucketOut w x y t u := by
    intro t u
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [hentry]
    unfold bucketOut
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hsq : (Real.sqrt (s : ℝ))⁻¹ * (Real.sqrt (s : ℝ))⁻¹ = 1 / (s : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg s), one_div]
  unfold sqNorm dotProduct
  rw [Fintype.sum_prod_type]
  simp only [hmv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [← hsq]
  ring

/-- Bucket mass `W_{tu} = ∑_{i : h_t(i) = u} z_i²`. -/
def bucketMass {s b n : ℕ} (z : Fin n → ℝ) (x : Fin s × Fin n → Fin b) (t : Fin s)
    (u : Fin b) : ℝ :=
  ∑ i, if x (t, i) = u then z i ^ 2 else 0

/-- Excess mass `𝓛 = ∑_{t,u} (W_{tu} - 10/D)_+`. -/
def excessMass {s b n : ℕ} (z : Fin n → ℝ) (D : ℝ) (x : Fin s × Fin n → Fin b) : ℝ :=
  ∑ t, ∑ u, max (bucketMass z x t u - 10 / D) 0

/-- Retained mass: `W_{tu}` if the bucket is retained (`W_{tu} ≤ 20/D`), else `0`. -/
def retainedMass {s b n : ℕ} (z : Fin n → ℝ) (D : ℝ) (x : Fin s × Fin n → Fin b) (t : Fin s)
    (u : Fin b) : ℝ :=
  if bucketMass z x t u ≤ 20 / D then bucketMass z x t u else 0

theorem bucketMass_nonneg {s b n : ℕ} (z : Fin n → ℝ) (x : Fin s × Fin n → Fin b) (t : Fin s)
    (u : Fin b) : 0 ≤ bucketMass z x t u :=
  Finset.sum_nonneg (fun i _ => by positivity)

/-- Each block carries total mass one: `∑_u W_{tu} = ∑_i p_i = 1`. -/
theorem sum_bucketMass {s b n : ℕ} (z : Fin n → ℝ) (hz1 : ∑ i, z i ^ 2 = 1)
    (x : Fin s × Fin n → Fin b) (t : Fin s) : ∑ u, bucketMass z x t u = 1 := by
  unfold bucketMass
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact hz1

end SmallBallAux

end

end SparseStack
