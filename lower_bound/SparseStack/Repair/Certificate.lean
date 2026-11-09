import SparseStack.Repair.Defs

/-!
# Head repair: the deterministic certificate core and the augmented background (HR5, HR7)
(paper, lines 1049–1093)

* `rep_sqNorm_nonneg`, `rep_dot_sq_le` (Cauchy–Schwarz), `sqNorm_restrictVec`: elementary facts.
* `sqNorm_mulVec_le_opNorm`: `‖A x‖² ≤ ‖A‖² ‖x‖²` for the L2 operator norm.
* `cert_core`: on `‖crossGram I V ω‖ ≤ t₀`, for all `h` supported on `I` and all `f`,
  `‖T Π h‖² - t₀ ‖h‖² ≤ ‖Π(h + V f)‖² + t₀ ‖f‖²` (delete the non-retained rows, expand the square,
  `2|hᵀ M f| ≤ t₀ (‖h‖² + ‖f‖²)`). Combined with W-SKETCH's `retained_head_gram`
  (`‖T Π h‖² = ∑_{i ∈ I} (a_i/s) h_i²`) it gives both certificates.
* `wPlus_isometry`, `wPlus_supp`, `wPlus_mulVec`, `sqNorm_wPlusCoeff`, `split_wPlus`: the augmented
  background `W₊ = [E_G | V]` of the second group.
-/

namespace SparseStack

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ## Elementary facts -/

theorem rep_sqNorm_nonneg {ι : Type} [Fintype ι] (v : ι → ℝ) : 0 ≤ sqNorm v := by
  unfold sqNorm dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

/-- Cauchy–Schwarz: `(v ⬝ w)² ≤ ‖v‖² ‖w‖²`. -/
theorem rep_dot_sq_le {ι : Type} [Fintype ι] (v w : ι → ℝ) :
    dotProduct v w ^ 2 ≤ sqNorm v * sqNorm w := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
  unfold sqNorm dotProduct
  simpa only [sq] using h

/-- `‖E_B h‖² = ∑_{i ∈ B} h_i²`. -/
theorem sqNorm_restrictVec {n : ℕ} (B : Finset (Fin n)) (h : Fin n → ℝ) :
    sqNorm (restrictVec B h) = ∑ i ∈ B, h i ^ 2 := by
  unfold sqNorm dotProduct restrictVec
  have hpt : ∀ i, (if i ∈ B then h i else 0) * (if i ∈ B then h i else 0) =
      if i ∈ B then h i ^ 2 else 0 := by
    intro i
    split_ifs <;> ring
  simp only [hpt]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

/-! ## Operator norm and the certificate core -/

/-- `‖A x‖² ≤ ‖A‖² ‖x‖²` for the L2 operator norm. -/
theorem sqNorm_mulVec_le_opNorm {m k : Type} [Fintype m] [Fintype k] [DecidableEq m]
    [DecidableEq k] (A : Matrix m k ℝ) (x : k → ℝ) :
    sqNorm (A.mulVec x) ≤ ‖A‖ ^ 2 * sqNorm x := by
  let xE : EuclideanSpace ℝ k := WithLp.toLp 2 x
  let yE : EuclideanSpace ℝ m := (EuclideanSpace.equiv m ℝ).symm (Matrix.mulVec A xE)
  have hop : ‖yE‖ ≤ ‖A‖ * ‖xE‖ := by
    simpa [yE] using Matrix.l2_opNorm_mulVec A xE
  have hx : ‖xE‖ ^ 2 = sqNorm x := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [xE, sqNorm, dotProduct, sq]
  have hy : ‖yE‖ ^ 2 = sqNorm (A.mulVec x) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [yE, xE, sqNorm, dotProduct, sq]
  calc sqNorm (A.mulVec x) = ‖yE‖ ^ 2 := hy.symm
    _ ≤ (‖A‖ * ‖xE‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hop 2
    _ = ‖A‖ ^ 2 * sqNorm x := by rw [mul_pow, hx]

/-- Deleting rows (a diagonal `0/1` matrix) does not increase the squared norm. -/
theorem sqNorm_retain_mulVec_le {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n)
    (y : Fin s × Fin b → ℝ) : sqNorm ((retainMatrix I ω).mulVec y) ≤ sqNorm y := by
  unfold sqNorm dotProduct retainMatrix
  apply Finset.sum_le_sum
  intro p _
  rw [Matrix.mulVec_diagonal]
  split_ifs
  · simp
  · simp only [zero_mul]
    exact mul_self_nonneg (y p)

/-- Certificate core: on the cross-Gram success event, for all `h` supported on `I` and all `f`,
`‖T Π h‖² - t₀ ‖h‖² ≤ ‖Π(h + V f)‖² + t₀ ‖f‖²`, where `T = retainMatrix I ω`. -/
theorem cert_core {s b n d : ℕ} (I : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ)
    (ω : SketchSample s b n) (hM : ‖crossGram I V ω‖ ≤ t0)
    (h : Fin n → ℝ) (hh : ∀ i, i ∉ I → h i = 0) (f : Fin d → ℝ) :
    sqNorm ((retainMatrix I ω).mulVec ((sketchMatrix ω).mulVec h)) - t0 * sqNorm h ≤
      sqNorm ((sketchMatrix ω).mulVec (h + V.mulVec f)) + t0 * sqNorm f := by
  -- the head part is unchanged by `E_I`
  have hPh : (coordProj I).mulVec h = h := by
    funext i
    rw [coordProj, Matrix.mulVec_diagonal]
    by_cases hi : i ∈ I
    · simp [hi]
    · simp [hi, hh i hi]
  have hA : (retainMatrix I ω * sketchMatrix ω * coordProj I).mulVec h =
      (retainMatrix I ω).mulVec ((sketchMatrix ω).mulVec h) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPh]
  have hC : (retainMatrix I ω * sketchMatrix ω * V).mulVec f =
      (retainMatrix I ω).mulVec ((sketchMatrix ω).mulVec (V.mulVec f)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  -- the cross term is `hᵀ M f`
  have hinner : dotProduct ((retainMatrix I ω).mulVec ((sketchMatrix ω).mulVec h))
      ((retainMatrix I ω).mulVec ((sketchMatrix ω).mulVec (V.mulVec f))) =
      dotProduct h ((crossGram I V ω).mulVec f) := by
    have e1 : (crossGram I V ω).mulVec f =
        (retainMatrix I ω * sketchMatrix ω * coordProj I).transpose.mulVec
          ((retainMatrix I ω * sketchMatrix ω * V).mulVec f) := by
      rw [crossGram, Matrix.mulVec_mulVec]
    rw [e1, Matrix.dotProduct_mulVec h, Matrix.vecMul_transpose, hA, hC]
  -- expand the square and delete rows
  have hsplit : (retainMatrix I ω).mulVec ((sketchMatrix ω).mulVec (h + V.mulVec f)) =
      (retainMatrix I ω).mulVec ((sketchMatrix ω).mulVec h) +
        (retainMatrix I ω).mulVec ((sketchMatrix ω).mulVec (V.mulVec f)) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add]
  have hdel := sqNorm_retain_mulVec_le I ω ((sketchMatrix ω).mulVec (h + V.mulVec f))
  rw [hsplit] at hdel
  -- `‖M f‖² ≤ t₀² ‖f‖²` and Cauchy–Schwarz
  have hMf : sqNorm ((crossGram I V ω).mulVec f) ≤ t0 ^ 2 * sqNorm f := by
    have h1 := sqNorm_mulVec_le_opNorm (crossGram I V ω) f
    have h2 : ‖crossGram I V ω‖ ^ 2 ≤ t0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hM 2
    have h3 := rep_sqNorm_nonneg f
    nlinarith
  have hCS := rep_dot_sq_le h ((crossGram I V ω).mulVec f)
  rw [← hinner] at hCS
  generalize (retainMatrix I ω).mulVec ((sketchMatrix ω).mulVec h) = a at hdel hCS ⊢
  generalize (retainMatrix I ω).mulVec ((sketchMatrix ω).mulVec (V.mulVec f)) = c at hdel hCS
  generalize sqNorm ((crossGram I V ω).mulVec f) = X at hMf hCS
  -- `2 |hᵀ M f| ≤ t₀ (‖h‖² + ‖f‖²)`
  have hH := rep_sqNorm_nonneg h
  have hF := rep_sqNorm_nonneg f
  have ht0 : (0 : ℝ) ≤ t0 := by norm_num [t0]
  have hz2 : (2 * dotProduct a c) ^ 2 ≤ (t0 * (sqNorm h + sqNorm f)) ^ 2 := by
    have k1 := mul_le_mul_of_nonneg_left hMf hH
    have k2 : 0 ≤ t0 ^ 2 * (sqNorm h - sqNorm f) ^ 2 := by positivity
    nlinarith
  have hcross : -(t0 * (sqNorm h + sqNorm f)) ≤ 2 * dotProduct a c :=
    (abs_le_of_sq_le_sq' hz2 (by positivity)).1
  have hexp : sqNorm (a + c) = sqNorm a + 2 * dotProduct a c + sqNorm c := by
    unfold sqNorm
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm c a]
    ring
  rw [hexp] at hdel
  have hc0 := rep_sqNorm_nonneg c
  linarith

/-! ## The augmented background `W₊ = [E_G | V]` -/

/-- `E_Gᵀ E_G = I`. -/
theorem coordCols_isometry {n : ℕ} (G : Finset (Fin n)) :
    (coordCols G).transpose * coordCols G = 1 := by
  ext j j'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, coordCols, Matrix.one_apply]
  rw [Finset.sum_eq_single (G.equivFin.symm j : Fin n)]
  · by_cases hjj : j = j'
    · subst hjj
      simp
    · have hne : (G.equivFin.symm j : Fin n) ≠ (G.equivFin.symm j' : Fin n) := by
        intro heq
        exact hjj (G.equivFin.symm.injective (Subtype.ext heq))
      simp [hne, hjj]
  · intro i _ hi
    simp [hi]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- `E_Gᵀ V = 0` when `V` vanishes on the rows of `G`. -/
theorem coordCols_transpose_mul {n d : ℕ} (G : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ)
    (hVsupp : ∀ i ∈ G, ∀ k, V i k = 0) : (coordCols G).transpose * V = 0 := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, coordCols, Matrix.zero_apply]
  rw [Finset.sum_eq_single (G.equivFin.symm j : Fin n)]
  · simp [hVsupp _ (G.equivFin.symm j).2 k]
  · intro i _ hi
    simp [hi]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- `W₊ = [E_G | V]` is an isometry when `V` is an isometry vanishing on the rows of `G`. -/
theorem wPlus_isometry {n d : ℕ} (G : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ)
    (hV : V.transpose * V = 1) (hVsupp : ∀ i ∈ G, ∀ k, V i k = 0) :
    (wPlus G V).transpose * wPlus G V = 1 := by
  have hEV := coordCols_transpose_mul G V hVsupp
  have hVE : V.transpose * coordCols G = 0 := by
    rw [← Matrix.transpose_transpose (V.transpose * coordCols G), Matrix.transpose_mul,
      Matrix.transpose_transpose, hEV, Matrix.transpose_zero]
  rw [wPlus, Matrix.transpose_submatrix,
    ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.transpose_fromCols,
    Matrix.fromRows_mul_fromCols, coordCols_isometry, hEV, hVE, hV, Matrix.fromBlocks_one,
    Matrix.submatrix_one_equiv]

/-- `W₊` vanishes on the rows of `B` when `B` is disjoint from `G` and `V` vanishes on `B`. -/
theorem wPlus_supp {n d : ℕ} (B G : Finset (Fin n)) (hBG : Disjoint B G)
    (V : Matrix (Fin n) (Fin d) ℝ) (hVsupp : ∀ i ∈ B, ∀ k, V i k = 0) :
    ∀ i ∈ B, ∀ k, wPlus G V i k = 0 := by
  intro i hi k
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective k
  simp only [wPlus, Matrix.submatrix_apply, id, Equiv.symm_apply_apply]
  cases x with
  | inl j =>
    rw [Matrix.fromCols_apply_inl, coordCols, if_neg]
    intro hij
    have hmem : (G.equivFin.symm j : Fin n) ∈ G := (G.equivFin.symm j).2
    rw [← hij] at hmem
    exact Finset.disjoint_left.1 hBG hi hmem
  | inr k' =>
    rw [Matrix.fromCols_apply_inr]
    exact hVsupp i hi k'

/-- `E_G (h ∘ g) = E_G h`: the coordinate columns applied to the restriction of `h` to `G`. -/
theorem coordCols_mulVec {n : ℕ} (G : Finset (Fin n)) (h : Fin n → ℝ) :
    (coordCols G).mulVec (fun j => h (G.equivFin.symm j : Fin n)) = restrictVec G h := by
  funext i
  simp only [Matrix.mulVec, dotProduct, coordCols, restrictVec, ite_mul, one_mul, zero_mul]
  rw [G.equivFin.symm.sum_comp (fun x : G => if i = (x : Fin n) then h x else 0)]
  rw [Finset.sum_coe_sort (s := G) (f := fun x => if i = x then h x else 0)]
  exact Finset.sum_ite_eq G i h

/-- `W₊ (h|_G, f) = E_G h + V f`. -/
theorem wPlus_mulVec {n d : ℕ} (G : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ)
    (h : Fin n → ℝ) (f : Fin d → ℝ) :
    (wPlus G V).mulVec (wPlusCoeff G h f) = restrictVec G h + V.mulVec f := by
  rw [wPlus, Matrix.submatrix_mulVec_equiv]
  have hco : wPlusCoeff G h f ∘ ⇑finSumFinEquiv.symm.symm =
      Sum.elim (fun j : Fin G.card => h (G.equivFin.symm j : Fin n)) f := by
    funext x
    simp [wPlusCoeff]
  rw [hco, Matrix.fromCols_mulVec_sumElim, coordCols_mulVec]
  rfl

/-- `‖(h|_G, f)‖² = ‖h_G‖² + ‖f‖²`. -/
theorem sqNorm_wPlusCoeff {n d : ℕ} (G : Finset (Fin n)) (h : Fin n → ℝ) (f : Fin d → ℝ) :
    sqNorm (wPlusCoeff G h f) = ∑ i ∈ G, h i ^ 2 + sqNorm f := by
  unfold sqNorm dotProduct wPlusCoeff
  rw [← finSumFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  congr 1
  rw [← Finset.sum_coe_sort (s := G) (f := fun i => h i ^ 2),
    ← G.equivFin.symm.sum_comp (fun x : G => h (x : Fin n) ^ 2)]
  simp only [sq]

/-- For `h` supported on `B ∪ G` (disjoint): `h + V f = E_B h + W₊ (h|_G, f)`. -/
theorem split_wPlus {n d : ℕ} (B G : Finset (Fin n)) (hBG : Disjoint B G)
    (V : Matrix (Fin n) (Fin d) ℝ) (h : Fin n → ℝ) (hh : ∀ i, i ∉ B ∪ G → h i = 0)
    (f : Fin d → ℝ) :
    h + V.mulVec f = restrictVec B h + (wPlus G V).mulVec (wPlusCoeff G h f) := by
  rw [wPlus_mulVec]
  funext i
  simp only [Pi.add_apply, restrictVec]
  by_cases hB : i ∈ B
  · have hG : i ∉ G := Finset.disjoint_left.1 hBG hB
    simp [hB, hG]
  · by_cases hG : i ∈ G
    · simp [hB, hG]
    · have h0 : h i = 0 := hh i (by simp [hB, hG])
      simp [hB, hG, h0]

end SparseStack
