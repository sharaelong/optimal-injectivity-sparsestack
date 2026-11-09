import SparseStack.Basic.Defs

/-!
# Linear-algebra steps of Case B (paper, lines 1298–1326)

* `background_basis` (lines 1298–1304): the column space `W` of `E_{Iᶜ} Q` (rows in `I` set to
  zero), viewed inside `EuclideanSpace ℝ (Fin n)`, has an orthonormal basis
  (`stdOrthonormalBasis`); its vectors are the columns of `V`, so `Vᵀ V = 1`, `d = dim W ≤ r`, the
  rows of `V` in `I` vanish, and `B_J = Vᵀ E_{Iᶜ} Q` satisfies `E_{Iᶜ} Q x = V B_J x` because
  `V Vᵀ` is the identity on `W` (`OrthonormalBasis.sum_repr'`).
* `caseB_combine` (lines 1311–1326): with `h = E_I Q x`, `f = B_J x`, `c_x = ∑_{i ∉ I} (Qx)_i²`:
  `Qx = h + V f`, `‖h‖² = ‖x‖² - c_x` (`Q` isometry), `‖f‖² = c_x` (`V` isometry); then
  `β (‖x‖² - c_x) ≤ Y + t₀ c_x` and `c_x ≤ u ‖x‖² + v X` give
  `(β - γ u) ‖x‖² ≤ Y + γ v X ≤ γ v (X + Y)` (`γ = β + t₀`, `γ v ≥ 1`), and
  `A ≥ c (X + Y) ≥ ρ₀ (X + Y) ≥ ρ₀ (β - γ u)/(γ v) ‖x‖² = α ‖x‖²`.
-/

namespace SparseStack

open Matrix

namespace CaseBLin

/-- An isometry (`Qᵀ Q = 1`) preserves `sqNorm`. -/
theorem sqNorm_mulVec_isometry {k l : Type} [Fintype k] [Fintype l] [DecidableEq l]
    (Q : Matrix k l ℝ) (hQ : Q.transpose * Q = 1) (x : l → ℝ) :
    sqNorm (Q.mulVec x) = sqNorm x := by
  unfold sqNorm
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
    Matrix.one_mulVec]

/-- `‖E_I w‖² + ∑_{i ∉ I} w_i² = ‖w‖²`. -/
theorem sqNorm_restrict_add {n : ℕ} (I : Finset (Fin n)) (w : Fin n → ℝ) :
    sqNorm (fun i => if i ∈ I then w i else 0) + ∑ i ∈ Iᶜ, w i ^ 2 = sqNorm w := by
  unfold sqNorm dotProduct
  have h1 : ∀ i, (if i ∈ I then w i else 0) * (if i ∈ I then w i else 0) =
      if i ∈ I then w i ^ 2 else 0 := by
    intro i
    by_cases hi : i ∈ I
    · rw [if_pos hi, if_pos hi, sq]
    · rw [if_neg hi, if_neg hi, mul_zero]
  simp only [h1]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_add_sum_compl I (fun i => w i ^ 2)]
  apply Finset.sum_congr rfl
  intro i _
  rw [sq]

/-- `‖E_{Iᶜ} w‖² = ∑_{i ∉ I} w_i²`. -/
theorem sqNorm_restrict_compl {n : ℕ} (I : Finset (Fin n)) (w : Fin n → ℝ) :
    sqNorm (fun i => if i ∈ I then 0 else w i) = ∑ i ∈ Iᶜ, w i ^ 2 := by
  unfold sqNorm dotProduct
  have h1 : ∀ i, (if i ∈ I then 0 else w i) * (if i ∈ I then 0 else w i) =
      if i ∈ Iᶜ then w i ^ 2 else 0 := by
    intro i
    by_cases hi : i ∈ I
    · have hi' : i ∉ Iᶜ := fun h => (Finset.mem_compl.mp h) hi
      rw [if_pos hi, if_neg hi', mul_zero]
    · have hi' : i ∈ Iᶜ := Finset.mem_compl.mpr hi
      rw [if_neg hi, if_pos hi', sq]
  simp only [h1]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

end CaseBLin

open CaseBLin

/-- Background basis (paper, lines 1298–1304): for every coordinate set `I` there are `d ≤ r`, an
isometry `V ∈ ℝ^{n×d}` supported off `I`, and `B_J ∈ ℝ^{d×r}` with `E_{Iᶜ} Q x = V B_J x`. -/
theorem background_basis {n r : ℕ} (Q : Matrix (Fin n) (Fin r) ℝ) (I : Finset (Fin n)) :
    ∃ (d : ℕ) (V : Matrix (Fin n) (Fin d) ℝ) (BJ : Matrix (Fin d) (Fin r) ℝ),
      d ≤ r ∧ V.transpose * V = 1 ∧ (∀ i ∈ I, ∀ k, V i k = 0) ∧
        ∀ x, (fun i => if i ∈ I then 0 else Q.mulVec x i) = V.mulVec (BJ.mulVec x) := by
  classical
  -- the matrix `E_{Iᶜ} Q`
  let P : Matrix (Fin n) (Fin r) ℝ := Matrix.of fun i j => if i ∈ I then 0 else Q i j
  have hP : ∀ x, (fun i => if i ∈ I then 0 else Q.mulVec x i) = P.mulVec x := by
    intro x
    funext i
    by_cases hi : i ∈ I
    · simp [P, Matrix.mulVec, dotProduct, hi]
    · simp [P, Matrix.mulVec, dotProduct, hi]
  -- its column space inside Euclidean space, and an orthonormal basis of it
  let L : (Fin r → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap ∘ₗ Matrix.toLin' P
  have hL : ∀ x, L x = WithLp.toLp 2 (P.mulVec x) := fun x => rfl
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := LinearMap.range L
  let b := stdOrthonormalBasis ℝ W
  let d := Module.finrank ℝ W
  let V : Matrix (Fin n) (Fin d) ℝ :=
    Matrix.of fun i k => ((b k : W) : EuclideanSpace ℝ (Fin n)) i
  have hVcol : ∀ k, ((b k : W) : EuclideanSpace ℝ (Fin n)) ∈ W := fun k => (b k).2
  refine ⟨d, V, V.transpose * P, ?_, ?_, ?_, ?_⟩
  · -- `d ≤ r`
    have h1 := LinearMap.finrank_range_le L
    rw [Module.finrank_fin_fun] at h1
    exact h1
  · -- `Vᵀ V = 1`
    ext k l
    have horth := orthonormal_iff_ite.mp b.orthonormal k l
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at horth
    rw [Matrix.one_apply, ← horth]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, V, Matrix.of_apply, dotProduct,
      Pi.star_apply, star_trivial]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  · -- rows of `V` in `I` vanish
    intro i hi k
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hVcol k)
    simp only [V, Matrix.of_apply]
    rw [← hy, hL]
    simp [Matrix.mulVec, dotProduct, P, hi]
  · -- `E_{Iᶜ} Q x = V (Vᵀ E_{Iᶜ} Q x)`: `V Vᵀ` is the identity on `W`
    intro x
    rw [hP x, ← Matrix.mulVec_mulVec]
    generalize hy : P.mulVec x = y
    have hmem : WithLp.toLp 2 y ∈ W := ⟨x, by rw [hL x, hy]⟩
    have hrepr := b.sum_repr' ⟨WithLp.toLp 2 y, hmem⟩
    have h2 := congrArg (fun v : W => WithLp.ofLp (v : EuclideanSpace ℝ (Fin n))) hrepr
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner, WithLp.ofLp_sum,
      WithLp.ofLp_smul, EuclideanSpace.inner_eq_star_dotProduct] at h2
    conv_lhs => rw [← h2]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, V, Matrix.of_apply, Pi.star_apply, star_trivial]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _

/-- Deterministic combination (paper, lines 1311–1326), Rayleigh form. `Xx`, `Yx`, `Ax` are the
group-1, group-2 and full sketches applied to `Qx`. -/
theorem caseB_combine {n r d : ℕ} (Q : Matrix (Fin n) (Fin r) ℝ) (hQ : Q.transpose * Q = 1)
    (I : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ) (hV : V.transpose * V = 1)
    (BJ : Matrix (Fin d) (Fin r) ℝ)
    (hBJ : ∀ x, (fun i => if i ∈ I then 0 else Q.mulVec x i) = V.mulVec (BJ.mulVec x))
    (X Y A : (Fin n → ℝ) → ℝ) (c : ℝ) (hc : rho0 ≤ c)
    (hgroup : ∀ v, c * (X v + Y v) ≤ A v)
    (hcert : ∀ x, ∑ i ∈ Iᶜ, (Q.mulVec x i) ^ 2 ≤ uCert * sqNorm x + vCert * X (Q.mulVec x))
    (hrep : ∀ h : Fin n → ℝ, (∀ i, i ∉ I → h i = 0) → ∀ f : Fin d → ℝ,
      betaRep * sqNorm h ≤ Y (h + V.mulVec f) + t0 * sqNorm f)
    (hXnn : ∀ v, 0 ≤ X v) (hYnn : ∀ v, 0 ≤ Y v) :
    ∀ x, constAlpha * sqNorm x ≤ A (Q.mulVec x) := by
  intro x
  -- `h = E_I Q x`, `f = B_J x`, `Q x = h + V f`
  have hVf : V.mulVec (BJ.mulVec x) = fun i => if i ∈ I then 0 else Q.mulVec x i :=
    (hBJ x).symm
  have hsupp : ∀ i, i ∉ I → (fun i => if i ∈ I then Q.mulVec x i else 0) i = 0 := by
    intro i hi
    simp [hi]
  have hsum : (fun i => if i ∈ I then Q.mulVec x i else 0) + V.mulVec (BJ.mulVec x) =
      Q.mulVec x := by
    rw [hVf]
    funext i
    by_cases hi : i ∈ I
    · simp [hi]
    · simp [hi]
  -- the three squared norms
  have hnormw : sqNorm (Q.mulVec x) = sqNorm x := sqNorm_mulVec_isometry Q hQ x
  have hnormh : sqNorm (fun i => if i ∈ I then Q.mulVec x i else 0) =
      sqNorm x - ∑ i ∈ Iᶜ, (Q.mulVec x i) ^ 2 := by
    have h := sqNorm_restrict_add I (Q.mulVec x)
    linarith
  have hnormf : sqNorm (BJ.mulVec x) = ∑ i ∈ Iᶜ, (Q.mulVec x i) ^ 2 := by
    rw [← sqNorm_mulVec_isometry V hV (BJ.mulVec x), hVf, sqNorm_restrict_compl]
  -- the representation inequality, the tail certificate and the group bound
  have h1 := hrep (fun i => if i ∈ I then Q.mulVec x i else 0) hsupp (BJ.mulVec x)
  rw [hsum, hnormh, hnormf] at h1
  have h2 := hcert x
  have h3 := hgroup (Q.mulVec x)
  have hX := hXnn (Q.mulVec x)
  have hY := hYnn (Q.mulVec x)
  have h4 : rho0 * (X (Q.mulVec x) + Y (Q.mulVec x)) ≤ c * (X (Q.mulVec x) + Y (Q.mulVec x)) :=
    mul_le_mul_of_nonneg_right hc (add_nonneg hX hY)
  simp only [constAlpha, betaRep, t0, uCert, vCert, rho0] at h1 h2 h4 ⊢
  linarith

end SparseStack
