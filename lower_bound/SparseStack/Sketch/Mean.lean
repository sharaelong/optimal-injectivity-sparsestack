import SparseStack.Prob.Sketch

/-!
# Sketch identities: eq. (1) and block groups

Paper lines 43–50 (eq. (1)) and the group inequality (P4) of `prop:parameters` (line 1249).

## Proof notes (W-SKETCH)

* `mean_gram_eq_one`: entry `(i,j)` of `ΠᵀΠ` is `∑_{(t,u)} Π[(t,u),i] Π[(t,u),j]`. On the
  diagonal every term is `s⁻¹ [h_t(i) = u]` (signs square to one), so each column has unit norm
  (`sum_sketchMatrix_mul_self`). Off the diagonal, flipping the sign bits of coordinate `i`
  (`flipSign`, an involution of the sample space) negates the inner product, so its sum over the
  sample space vanishes (`sum_sketchMatrix_mul_of_ne`).
* `expect_frobSq`: `‖ΠU‖_F² = tr(Uᵀ (ΠᵀΠ) U)`, linearity of the mean, and `UᵀU = I`.
* `sqNorm_sketch_ge_groups`: `‖Π_s v‖² = s⁻¹ ∑_t W_t` with `W_t = ∑_u (∑_i [h_t(i)=u] σ_{ti} v_i)²`
  depending only on block `t`; a group of `q` blocks gives `q⁻¹ ∑_{t ∈ group} W_t`, and the two
  groups are disjoint.
-/

namespace SparseStack

open SparseFock

/-! ### Entries of the sketch -/

private theorem signValue_mul_self' (β : Bool) : signValue β * signValue β = 1 := by
  cases β <;> norm_num [signValue]

private theorem signValue_not' (β : Bool) : signValue (!β) = -signValue β := by
  cases β <;> norm_num [signValue]

private theorem inv_sqrt_mul_inv_sqrt (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ = x⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt hx]

/-- Squared entries of the sketch: `Π[(t,u),i]² = s⁻¹ [h_t(i) = u]`. -/
theorem sketchMatrix_mul_self {s b n : ℕ} (ω : SketchSample s b n) (p : Fin s × Fin b)
    (i : Fin n) :
    sketchMatrix ω p i * sketchMatrix ω p i =
      (s : ℝ)⁻¹ * (if ω.1 p.1 i = p.2 then 1 else 0) := by
  simp only [sketchMatrix]
  split_ifs
  · calc _ = ((Real.sqrt (s : ℝ))⁻¹ * (Real.sqrt (s : ℝ))⁻¹) *
          (signValue (ω.2 p.1 i) * signValue (ω.2 p.1 i)) := by ring
      _ = _ := by rw [inv_sqrt_mul_inv_sqrt _ (Nat.cast_nonneg s), signValue_mul_self', mul_one]
  · ring

/-- Every column of `Π` has unit norm (needs `s ≥ 1`). -/
theorem sum_sketchMatrix_mul_self {s b n : ℕ} (hs : 0 < s) (ω : SketchSample s b n)
    (i : Fin n) : ∑ p, sketchMatrix ω p i * sketchMatrix ω p i = 1 := by
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [sketchMatrix_mul_self]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ hs'

/-- Flip the sign bits of input coordinate `i` in every block. -/
def flipSign {s b n : ℕ} (i : Fin n) (ω : SketchSample s b n) : SketchSample s b n :=
  (ω.1, fun t k => if k = i then !(ω.2 t k) else ω.2 t k)

theorem flipSign_involutive {s b n : ℕ} (i : Fin n) :
    Function.Involutive (flipSign (s := s) (b := b) i) := by
  rintro ⟨h, σ⟩
  simp only [flipSign, Prod.mk.injEq, true_and]
  funext t k
  by_cases hk : k = i <;> simp [hk]

theorem sketchMatrix_flipSign_self {s b n : ℕ} (i : Fin n) (ω : SketchSample s b n)
    (p : Fin s × Fin b) : sketchMatrix (flipSign i ω) p i = -sketchMatrix ω p i := by
  have h2 : (flipSign i ω).2 p.1 i = !(ω.2 p.1 i) := by simp [flipSign]
  have h1 : (flipSign i ω).1 = ω.1 := rfl
  simp only [sketchMatrix, h1, h2]
  split_ifs
  · rw [signValue_not']
    ring
  · ring

theorem sketchMatrix_flipSign_of_ne {s b n : ℕ} {i j : Fin n} (hji : j ≠ i)
    (ω : SketchSample s b n) (p : Fin s × Fin b) :
    sketchMatrix (flipSign i ω) p j = sketchMatrix ω p j := by
  have h2 : (flipSign i ω).2 p.1 j = ω.2 p.1 j := by simp [flipSign, hji]
  have h1 : (flipSign i ω).1 = ω.1 := rfl
  simp only [sketchMatrix, h1, h2]

/-- Distinct columns have mean-zero inner products: flipping the signs of coordinate `i` negates
the inner product of columns `i ≠ j`, and `flipSign i` is a bijection of the sample space. -/
theorem sum_sketchMatrix_mul_of_ne {s b n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∑ ω : SketchSample s b n, ∑ p, sketchMatrix ω p i * sketchMatrix ω p j = 0 := by
  have hS : ∀ ω : SketchSample s b n,
      ∑ p, sketchMatrix (flipSign i ω) p i * sketchMatrix (flipSign i ω) p j =
        -∑ p, sketchMatrix ω p i * sketchMatrix ω p j := by
    intro ω
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [sketchMatrix_flipSign_self, sketchMatrix_flipSign_of_ne (Ne.symm hij), neg_mul]
  have h := Fintype.sum_equiv ((flipSign_involutive (s := s) (b := b) i).toPerm _)
    (fun ω => ∑ p, sketchMatrix (flipSign i ω) p i * sketchMatrix (flipSign i ω) p j)
    (fun ω => ∑ p, sketchMatrix ω p i * sketchMatrix ω p j) (fun _ => rfl)
  simp only [hS, Finset.sum_neg_distrib] at h
  linarith

/-- eq. (1): `E Πᵀ Π = I_n` for every `s ≥ 1`, `b ≥ 1` (columns have unit norm; distinct columns
have mean-zero inner products). -/
theorem mean_gram_eq_one {s b n : ℕ} (hs : 0 < s) (hb : 0 < b) :
    uniformMeanMatrix
        (fun ω : SketchSample s b n => (sketchMatrix ω).transpose * sketchMatrix ω) = 1 := by
  ext i j
  simp only [uniformMeanMatrix, Matrix.smul_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.transpose_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs with hij
  · subst hij
    simp only [sum_sketchMatrix_mul_self hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    exact inv_mul_cancel₀ (card_sketchSample_ne_zero hb)
  · rw [sum_sketchMatrix_mul_of_ne hij, mul_zero]

/-- `‖A‖_F² = tr(AᵀA)`. -/
theorem frobSq_eq_trace {k l : Type} [Fintype k] [Fintype l] (A : Matrix k l ℝ) :
    frobSq A = Matrix.trace (A.transpose * A) := by
  simp only [frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
  exact Finset.sum_comm

/-- `E ‖Π U‖_F² = D` for an isometry `U ∈ ℝ^{n×D}` (localization, line 395). -/
theorem expect_frobSq {s b n D : ℕ} (hs : 0 < s) (hb : 0 < b) (U : Matrix (Fin n) (Fin D) ℝ)
    (hU : U.transpose * U = 1) :
    (sketchLaw s b n hb).expect (fun ω => frobSq (sketchMatrix ω * U)) = D := by
  have key : (sketchLaw s b n hb).expect (fun ω => frobSq (sketchMatrix ω * U)) =
      Matrix.trace (U.transpose * uniformMeanMatrix
        (fun ω : SketchSample s b n => (sketchMatrix ω).transpose * sketchMatrix ω) * U) := by
    rw [sketchLaw_expect_eq_sum, div_eq_inv_mul]
    simp only [uniformMeanMatrix, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum,
      Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    rw [frobSq_eq_trace, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [key, mean_gram_eq_one hs hb, Matrix.mul_one, hU, Matrix.trace_one, Fintype.card_fin]

/-! ### Block groups (P4) -/

/-- Signed bucket sum `∑_i [h_t(i) = u] σ_{ti} v_i` of block `t`, bucket `u`. -/
noncomputable def sketchBucketSum {s b n : ℕ} (ω : SketchSample s b n) (v : Fin n → ℝ)
    (t : Fin s) (u : Fin b) : ℝ :=
  ∑ i, (if ω.1 t i = u then signValue (ω.2 t i) else 0) * v i

theorem sketchMatrix_mulVec_apply {s b n : ℕ} (ω : SketchSample s b n) (v : Fin n → ℝ)
    (p : Fin s × Fin b) :
    (sketchMatrix ω).mulVec v p = (Real.sqrt (s : ℝ))⁻¹ * sketchBucketSum ω v p.1 p.2 := by
  simp only [Matrix.mulVec, dotProduct, sketchMatrix, sketchBucketSum, Finset.mul_sum,
    mul_assoc]

/-- `‖Π_s v‖² = s⁻¹ ∑_t ∑_u (∑_i [h_t(i) = u] σ_{ti} v_i)²`. -/
theorem sqNorm_sketchMatrix_mulVec {s b n : ℕ} (ω : SketchSample s b n) (v : Fin n → ℝ) :
    sqNorm ((sketchMatrix ω).mulVec v) =
      (s : ℝ)⁻¹ * ∑ t, ∑ u, sketchBucketSum ω v t u ^ 2 := by
  simp only [sqNorm, dotProduct, sketchMatrix_mulVec_apply]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [← inv_sqrt_mul_inv_sqrt _ (Nat.cast_nonneg s)]
  ring

theorem sketchBucketSum_blockRestrict {s q b n : ℕ} (f : Fin q → Fin s)
    (ω : SketchSample s b n) (v : Fin n → ℝ) (t : Fin q) (u : Fin b) :
    sketchBucketSum (blockRestrict f ω) v t u = sketchBucketSum ω v (f t) u :=
  rfl

/-- The scalar step of (P4), including the degenerate cases `q = 0` and `s = 0`. -/
private theorem groups_scalar_ineq (q s : ℕ) {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hABC : A + B ≤ C) :
    (q : ℝ) / s * ((q : ℝ)⁻¹ * A + (q : ℝ)⁻¹ * B) ≤ (s : ℝ)⁻¹ * C := by
  have hs0 : (0 : ℝ) ≤ (s : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg s)
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp only [Nat.cast_zero, zero_div, zero_mul]
    exact mul_nonneg hs0 (by linarith)
  · have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have h : (q : ℝ) / s * ((q : ℝ)⁻¹ * A + (q : ℝ)⁻¹ * B) =
        ((q : ℝ) * (q : ℝ)⁻¹) * ((s : ℝ)⁻¹ * (A + B)) := by
      rw [div_eq_mul_inv]
      ring
    rw [h, mul_inv_cancel₀ hq', one_mul]
    exact mul_le_mul_of_nonneg_left hABC hs0

/-- Group inequality (P4): for two disjoint groups of `q` blocks, each normalized by `q^{-1/2}`,
`‖Π_s v‖² ≥ (q/s) (‖Π_q^{(1)} v‖² + ‖Π_q^{(2)} v‖²)`. -/
theorem sqNorm_sketch_ge_groups {s q b n : ℕ} (f₁ f₂ : Fin q → Fin s)
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂) (hdisj : ∀ t₁ t₂, f₁ t₁ ≠ f₂ t₂)
    (ω : SketchSample s b n) (v : Fin n → ℝ) :
    (q : ℝ) / s * (sqNorm ((sketchMatrix (blockRestrict f₁ ω)).mulVec v) +
        sqNorm ((sketchMatrix (blockRestrict f₂ ω)).mulVec v)) ≤
      sqNorm ((sketchMatrix ω).mulVec v) := by
  have hW0 : ∀ t, 0 ≤ ∑ u, sketchBucketSum ω v t u ^ 2 :=
    fun t => Finset.sum_nonneg (fun u _ => sq_nonneg _)
  have hX : ∀ f : Fin q → Fin s, sqNorm ((sketchMatrix (blockRestrict f ω)).mulVec v) =
      (q : ℝ)⁻¹ * ∑ t, ∑ u, sketchBucketSum ω v (f t) u ^ 2 := by
    intro f
    rw [sqNorm_sketchMatrix_mulVec]
    rfl
  rw [hX f₁, hX f₂, sqNorm_sketchMatrix_mulVec]
  have hg : Function.Injective (Sum.elim f₁ f₂) := hf₁.sumElim hf₂ hdisj
  have hsub : ∑ t, ∑ u, sketchBucketSum ω v (f₁ t) u ^ 2 +
      ∑ t, ∑ u, sketchBucketSum ω v (f₂ t) u ^ 2 ≤ ∑ t, ∑ u, sketchBucketSum ω v t u ^ 2 := by
    have h1 : ∑ t, ∑ u, sketchBucketSum ω v (f₁ t) u ^ 2 +
        ∑ t, ∑ u, sketchBucketSum ω v (f₂ t) u ^ 2 =
        ∑ t ∈ Finset.univ.map ⟨Sum.elim f₁ f₂, hg⟩, ∑ u, sketchBucketSum ω v t u ^ 2 := by
      rw [Finset.sum_map, Fintype.sum_sum_type]
      rfl
    rw [h1]
    exact Finset.sum_le_univ_sum_of_nonneg hW0
  exact groups_scalar_ineq q s (Finset.sum_nonneg fun t _ => hW0 _)
    (Finset.sum_nonneg fun t _ => hW0 _) hsub

end SparseStack
