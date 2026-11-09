import Mathlib

/-!
# Common-coordinate selection (separation step of `thm:linearization`)

Let `v_i = V i` be the rows of `V` and `H ⪰ 0`. Assume that for every density matrix `R` there is `S`,
`|S| ≤ j`, with `∑_{i ∉ S} v_iᵀ R v_i ≤ tr (R H)`. Then one set `I`, `|I| ≤ 2j`, satisfies
`∑_{i ∉ I} (v_i · x)² ≤ 2 xᵀ H x` for all `x`.

Proof (minimax by separation):
* `𝒲 = {w ∈ [0,1]ⁿ : ∑ wᵢ ≤ j}` is compact and convex, and `D(w) = ∑ᵢ (1 - wᵢ) vᵢ vᵢᵀ` is affine;
* `𝒰 = {M : ∃ w ∈ 𝒲, M - D(w) ⪰ 0} = D(𝒲) + PSD` is convex and closed;
* if `H ∉ 𝒰`, the geometric Hahn–Banach theorem gives a continuous functional `f` and `u` with
  `f H < u < f U` for `U ∈ 𝒰`. Writing `f M = tr (Gᵀ M)` and `R₀ = Gᵀ + G` we get
  `2 f M = tr (R₀ M)` for symmetric `M`; `𝒰 + PSD ⊆ 𝒰` forces `R₀ ⪰ 0`; `R₀ ≠ 0`; with
  `R = R₀ / tr R₀` the hypothesis provides `S`, and `w = 1_S ∈ 𝒲` gives
  `tr (R₀ D(w)) ≤ tr (R₀ H)`, contradicting `f H < u < f (D w)`;
* hence `D(w) ⪯ H` for some `w ∈ 𝒲`; take `I = {i : wᵢ ≥ 1/2}`: `|I| ≤ 2 ∑ wᵢ ≤ 2j` and
  `∑_{i ∉ I} (vᵢ · x)² ≤ 2 ∑ᵢ (1 - wᵢ) (vᵢ · x)² = 2 xᵀ D(w) x ≤ 2 xᵀ H x`.
-/

namespace SparseStack

namespace Selection

open Matrix
open scoped Pointwise

variable {n d : ℕ}

/-- `D(w) = ∑ᵢ (1 - wᵢ) vᵢ vᵢᵀ`. -/
noncomputable def Dw (V : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ i, (1 - w i) • vecMulVec (V i) (V i)

/-- The weight polytope `𝒲 = {w ∈ [0,1]ⁿ : ∑ wᵢ ≤ j}`. -/
def Wset (n j : ℕ) : Set (Fin n → ℝ) := {w | (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧ ∑ i, w i ≤ j}

/-- `𝒰 = {M : ∃ w ∈ 𝒲, M - D(w) ⪰ 0}`. -/
def Uset (V : Matrix (Fin n) (Fin d) ℝ) (j : ℕ) : Set (Matrix (Fin d) (Fin d) ℝ) :=
  {M | ∃ w ∈ Wset n j, (M - Dw V w).PosSemidef}

theorem zero_mem_Wset (n j : ℕ) : (0 : Fin n → ℝ) ∈ Wset n j :=
  ⟨fun i => by simp, by simp⟩

theorem convex_Wset (n j : ℕ) : Convex ℝ (Wset n j) := by
  intro w₁ hw₁ w₂ hw₂ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨h1, h2⟩ := hw₁.1 i
    obtain ⟨h3, h4⟩ := hw₂.1 i
    constructor <;> nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := hw₁.2
    have h2 := hw₂.2
    nlinarith

theorem isCompact_Wset (n j : ℕ) : IsCompact (Wset n j) := by
  have h : Wset n j =
      (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) ∩ {w | ∑ i, w i ≤ (j : ℝ)} := by
    ext w
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun i _ => h1 i, h2⟩,
      fun ⟨h1, h2⟩ => ⟨fun i => h1 i (Set.mem_univ i), h2⟩⟩
  rw [h]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

theorem continuous_Dw (V : Matrix (Fin n) (Fin d) ℝ) : Continuous (Dw V) := by
  unfold Dw
  exact continuous_finsetSum _ fun i _ =>
    (continuous_const.sub (continuous_apply i)).smul continuous_const

theorem Dw_combo (V : Matrix (Fin n) (Fin d) ℝ) (w₁ w₂ : Fin n → ℝ) (a b : ℝ)
    (hab : a + b = 1) : Dw V (a • w₁ + b • w₂) = a • Dw V w₁ + b • Dw V w₂ := by
  unfold Dw
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, smul_smul, ← add_smul]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -hab

theorem convex_Uset (V : Matrix (Fin n) (Fin d) ℝ) (j : ℕ) : Convex ℝ (Uset V j) := by
  rintro M₁ ⟨w₁, hw₁, h₁⟩ M₂ ⟨w₂, hw₂, h₂⟩ a b ha hb hab
  refine ⟨a • w₁ + b • w₂, convex_Wset n j hw₁ hw₂ ha hb hab, ?_⟩
  rw [Dw_combo V w₁ w₂ a b hab]
  have e : a • M₁ + b • M₂ - (a • Dw V w₁ + b • Dw V w₂) =
      a • (M₁ - Dw V w₁) + b • (M₂ - Dw V w₂) := by
    simp only [smul_sub]
    abel
  rw [e]
  exact (h₁.smul ha).add (h₂.smul hb)

theorem isClosed_posSemidef : IsClosed {S : Matrix (Fin d) (Fin d) ℝ | S.PosSemidef} := by
  have h : {S : Matrix (Fin d) (Fin d) ℝ | S.PosSemidef} =
      {S | Sᴴ = S} ∩ ⋂ x : Fin d → ℝ, {S | 0 ≤ star x ⬝ᵥ (S *ᵥ x)} := by
    ext S
    rw [Set.mem_inter_iff, Set.mem_iInter]
    exact Matrix.posSemidef_iff_dotProduct_mulVec
  rw [h]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => ?_)
  exact isClosed_le continuous_const
    (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

theorem Uset_eq (V : Matrix (Fin n) (Fin d) ℝ) (j : ℕ) :
    Uset V j = (Dw V '' Wset n j) + {S : Matrix (Fin d) (Fin d) ℝ | S.PosSemidef} := by
  ext M
  rw [Set.mem_add]
  constructor
  · rintro ⟨w, hw, hM⟩
    exact ⟨Dw V w, ⟨w, hw, rfl⟩, M - Dw V w, hM, by abel⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, S, hS, rfl⟩
    refine ⟨w, hw, ?_⟩
    simpa using hS

theorem isClosed_Uset (V : Matrix (Fin n) (Fin d) ℝ) (j : ℕ) : IsClosed (Uset V j) := by
  rw [Uset_eq]
  exact isClosed_posSemidef.add_left_of_isCompact ((isCompact_Wset n j).image (continuous_Dw V))

/-- The coefficient matrix `G a b = f (E_ab)` of a linear functional on matrices. -/
noncomputable def funMat (f : Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b => f (Matrix.single a b 1)

/-- Every continuous linear functional on matrices is `M ↦ tr (Gᵀ M)`. -/
theorem clm_eq_trace (f : Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    f M = ((funMat f)ᵀ * M).trace := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    funMat, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [show Matrix.single a b (M a b) = M a b • Matrix.single a b (1 : ℝ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one],
    map_smul, smul_eq_mul, mul_comm]

/-- For symmetric `M`: `2 f M = tr ((Gᵀ + G) M)`. -/
theorem two_mul_clm_eq_trace (f : Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : Mᵀ = M) :
    2 * f M = (((funMat f)ᵀ + funMat f) * M).trace := by
  have h1 : (funMat f * M).trace = ((funMat f)ᵀ * M).trace := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, hM, Matrix.trace_mul_comm]
  rw [Matrix.add_mul, Matrix.trace_add, h1, ← clm_eq_trace]
  ring

theorem trace_mul_vecMulVec_self (R : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    (R * vecMulVec v v).trace = v ⬝ᵥ (R *ᵥ v) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem dotProduct_vecMulVec_mulVec (v x : Fin d → ℝ) :
    x ⬝ᵥ (vecMulVec v v *ᵥ x) = (v ⬝ᵥ x) ^ 2 := by
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm x v,
    sq]

theorem Dw_transpose (V : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ) : (Dw V w)ᵀ = Dw V w := by
  unfold Dw
  rw [Matrix.transpose_sum]
  simp only [Matrix.transpose_smul, Matrix.transpose_vecMulVec]

theorem trace_mul_Dw (R : Matrix (Fin d) (Fin d) ℝ) (V : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) : (R * Dw V w).trace = ∑ i, (1 - w i) * (V i ⬝ᵥ (R *ᵥ V i)) := by
  unfold Dw
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp only [Matrix.mul_smul, Matrix.trace_smul, trace_mul_vecMulVec_self, smul_eq_mul]

theorem dotProduct_Dw_mulVec (V : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (Dw V w *ᵥ x) = ∑ i, (1 - w i) * (V i ⬝ᵥ x) ^ 2 := by
  unfold Dw
  rw [Matrix.sum_mulVec, dotProduct_sum]
  simp only [Matrix.smul_mulVec, dotProduct_smul, dotProduct_vecMulVec_mulVec, smul_eq_mul]

/-- The separation step: some `w ∈ 𝒲` has `D(w) ⪯ H`. -/
theorem exists_Dw_le (V : Matrix (Fin n) (Fin d) ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (hH : Hᵀ = H) {j : ℕ}
    (hdual : ∀ R : Matrix (Fin d) (Fin d) ℝ, R.PosSemidef → R.trace = 1 →
      ∃ S : Finset (Fin n), S.card ≤ j ∧
        ∑ i ∈ Sᶜ, dotProduct (V i) (R.mulVec (V i)) ≤ (R * H).trace) :
    ∃ w ∈ Wset n j, (H - Dw V w).PosSemidef := by
  by_contra hcon
  have hnot : H ∉ Uset V j := hcon
  have : LocallyConvexSpace ℝ (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (LocallyConvexSpace ℝ (Fin d → Fin d → ℝ))
  obtain ⟨f, u, hfH, hfU⟩ :=
    geometric_hahn_banach_point_closed (convex_Uset V j) (isClosed_Uset V j) hnot
  set R₀ : Matrix (Fin d) (Fin d) ℝ := (funMat f)ᵀ + funMat f with hR₀def
  have hR₀T : R₀ᵀ = R₀ := by
    rw [hR₀def, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hpair : ∀ M : Matrix (Fin d) (Fin d) ℝ, Mᵀ = M → 2 * f M = (R₀ * M).trace :=
    fun M hM => two_mul_clm_eq_trace f M hM
  have hD0 : Dw V 0 ∈ Uset V j := ⟨0, zero_mem_Wset n j, by simpa using PosSemidef.zero⟩
  -- `f ≥ 0` on the PSD cone, since `𝒰 + PSD ⊆ 𝒰`
  have hcone : ∀ S : Matrix (Fin d) (Fin d) ℝ, S.PosSemidef → 0 ≤ f S := by
    intro S hS
    by_contra hneg'
    have hneg : f S < 0 := lt_of_not_ge hneg'
    have hfS : f S ≠ 0 := hneg.ne
    have hgap : 0 < f (Dw V 0) - u := by linarith [hfU _ hD0]
    have ht0 : 0 ≤ (f (Dw V 0) - u) / (-f S) := div_nonneg hgap.le (by linarith)
    have hmem : Dw V 0 + ((f (Dw V 0) - u) / (-f S)) • S ∈ Uset V j :=
      ⟨0, zero_mem_Wset n j, by simpa using hS.smul ht0⟩
    have h1 := hfU _ hmem
    rw [map_add, map_smul, smul_eq_mul] at h1
    have h2 : (f (Dw V 0) - u) / (-f S) * f S = -(f (Dw V 0) - u) := by
      rw [div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hfS, mul_one]
    linarith
  -- `R₀ ⪰ 0`
  have hR₀psd : R₀.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr hR₀T)
      fun x => ?_
    have hx : (vecMulVec x x).PosSemidef := by
      simpa using Matrix.posSemidef_vecMulVec_self_star x
    have hxT : (vecMulVec x x)ᵀ = vecMulVec x x := Matrix.transpose_vecMulVec x x
    have h := hpair _ hxT
    rw [trace_mul_vecMulVec_self] at h
    rw [star_trivial]
    linarith [hcone _ hx]
  -- `R₀ ≠ 0`
  have hHU : f H < f (Dw V 0) := lt_trans hfH (hfU _ hD0)
  have hR₀ne : R₀ ≠ 0 := by
    intro h0
    have e1 := hpair H hH
    have e2 := hpair (Dw V 0) (Dw_transpose V 0)
    rw [h0, Matrix.zero_mul, Matrix.trace_zero] at e1 e2
    linarith
  have htr : 0 < R₀.trace := by
    rcases hR₀psd.trace_nonneg.lt_or_eq with h | h
    · exact h
    · exact absurd (hR₀psd.trace_eq_zero_iff.mp h.symm) hR₀ne
  -- the density matrix `R = R₀ / tr R₀`
  have hRpsd : (R₀.trace⁻¹ • R₀).PosSemidef := hR₀psd.smul (inv_nonneg.mpr htr.le)
  have hRtr : (R₀.trace⁻¹ • R₀).trace = 1 := by
    rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ htr.ne']
  have hR₀R : R₀ = R₀.trace • (R₀.trace⁻¹ • R₀) := by
    rw [smul_smul, mul_inv_cancel₀ htr.ne', one_smul]
  obtain ⟨S, hScard, hSineq⟩ := hdual _ hRpsd hRtr
  -- the weight `w = 1_S`
  have hwW : (fun i => if i ∈ S then (1 : ℝ) else 0) ∈ Wset n j := by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases hi : i ∈ S <;> simp [hi]
    · have hsum : ∑ i, (if i ∈ S then (1 : ℝ) else 0) = S.card := by simp
      rw [hsum]
      exact_mod_cast hScard
  have hDwmem : Dw V (fun i => if i ∈ S then (1 : ℝ) else 0) ∈ Uset V j :=
    ⟨_, hwW, by simpa using PosSemidef.zero⟩
  have hDtr : ((R₀.trace⁻¹ • R₀) * Dw V (fun i => if i ∈ S then (1 : ℝ) else 0)).trace =
      ∑ i ∈ Sᶜ, V i ⬝ᵥ ((R₀.trace⁻¹ • R₀) *ᵥ V i) := by
    rw [trace_mul_Dw, ← Finset.sum_add_sum_compl S]
    have h1 : ∑ i ∈ S, (1 - (if i ∈ S then (1 : ℝ) else 0)) *
        (V i ⬝ᵥ ((R₀.trace⁻¹ • R₀) *ᵥ V i)) = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [hi]
    have h2 : ∑ i ∈ Sᶜ, (1 - (if i ∈ S then (1 : ℝ) else 0)) *
        (V i ⬝ᵥ ((R₀.trace⁻¹ • R₀) *ᵥ V i)) =
        ∑ i ∈ Sᶜ, V i ⬝ᵥ ((R₀.trace⁻¹ • R₀) *ᵥ V i) :=
      Finset.sum_congr rfl fun i hi => by simp [Finset.mem_compl.mp hi]
    rw [h1, h2, zero_add]
  have e1 := hpair H hH
  have e2 := hpair (Dw V (fun i => if i ∈ S then (1 : ℝ) else 0))
    (Dw_transpose V _)
  rw [hR₀R, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at e1 e2
  rw [hDtr] at e2
  have h3 := hfU _ hDwmem
  have h4 : R₀.trace * ∑ i ∈ Sᶜ, V i ⬝ᵥ ((R₀.trace⁻¹ • R₀) *ᵥ V i) ≤
      R₀.trace * ((R₀.trace⁻¹ • R₀) * H).trace :=
    mul_le_mul_of_nonneg_left hSineq htr.le
  linarith

end Selection

open Selection in
/-- Common-coordinate selection (separation step of `thm:linearization`): if every density matrix `R`
admits a set `S`, `|S| ≤ j`, with `∑_{i ∉ S} v_iᵀ R v_i ≤ tr(R H)`, then one set `I`, `|I| ≤ 2j`, works for
all `x` simultaneously with factor 2. Here `v_i = V i` is the i-th row of `V`. -/
theorem common_coordinate_selection {n d j : ℕ} (V : Matrix (Fin n) (Fin d) ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.PosSemidef)
    (hdual : ∀ R : Matrix (Fin d) (Fin d) ℝ, R.PosSemidef → R.trace = 1 →
      ∃ S : Finset (Fin n), S.card ≤ j ∧
        ∑ i ∈ Sᶜ, dotProduct (V i) (R.mulVec (V i)) ≤ (R * H).trace) :
    ∃ I : Finset (Fin n), I.card ≤ 2 * j ∧
      ∀ x : Fin d → ℝ, ∑ i ∈ Iᶜ, (V.mulVec x i) ^ 2 ≤ 2 * dotProduct x (H.mulVec x) := by
  obtain ⟨w, hw, hHD⟩ :=
    exists_Dw_le V H (Matrix.isHermitian_iff_isSymm.mp hH.isHermitian) hdual
  refine ⟨Finset.univ.filter (fun i => (1 : ℝ) / 2 ≤ w i), ?_, fun x => ?_⟩
  · -- `|I| / 2 ≤ ∑_{i ∈ I} wᵢ ≤ ∑ wᵢ ≤ j`
    have h1 : ((Finset.univ.filter (fun i => (1 : ℝ) / 2 ≤ w i)).card : ℝ) * (1 / 2) ≤
        ∑ i ∈ Finset.univ.filter (fun i => (1 : ℝ) / 2 ≤ w i), w i := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => (1 : ℝ) / 2 ≤ w i), w i ≤ ∑ i, w i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => (hw.1 i).1
    have h3 := hw.2
    have h4 : ((Finset.univ.filter (fun i => (1 : ℝ) / 2 ≤ w i)).card : ℝ) ≤ 2 * j := by
      linarith
    exact_mod_cast h4
  · have hq := dotProduct_Dw_mulVec V w x
    have hpsd := hHD.dotProduct_mulVec_nonneg x
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hq] at hpsd
    calc ∑ i ∈ (Finset.univ.filter (fun i => (1 : ℝ) / 2 ≤ w i))ᶜ, (V.mulVec x i) ^ 2
        ≤ ∑ i ∈ (Finset.univ.filter (fun i => (1 : ℝ) / 2 ≤ w i))ᶜ,
            2 * ((1 - w i) * (V i ⬝ᵥ x) ^ 2) := by
          apply Finset.sum_le_sum
          intro i hi
          have hwi : w i < 1 / 2 := by
            simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
              not_le] at hi
            exact hi
          have hsq := sq_nonneg (V i ⬝ᵥ x)
          have e : V.mulVec x i = V i ⬝ᵥ x := rfl
          rw [e]
          nlinarith
      _ ≤ ∑ i, 2 * ((1 - w i) * (V i ⬝ᵥ x) ^ 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro i _ _
          have h1 := (hw.1 i).2
          have hsq := sq_nonneg (V i ⬝ᵥ x)
          have h0 : 0 ≤ 1 - w i := by linarith
          exact mul_nonneg (by norm_num) (mul_nonneg h0 hsq)
      _ = 2 * ∑ i, (1 - w i) * (V i ⬝ᵥ x) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 2 * dotProduct x (H.mulVec x) := by linarith

end SparseStack
