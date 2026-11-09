import SparseStack.Rounding
import SparseFockFormal.FiniteProbability
import SparseStack.Lin.Rademacher
import SparseStack.Lin.TruncAux
import SparseStack.Lin.Selection

/-!
# Common-coordinate linearization (paper, lines 432–573)

* `truncation`: Lemma `lem:gaussian-truncation`, in the moment form actually used by its proof:
  only `E g_i²` and `E g_i⁴ ≤ 3 (E g_i²)²` matter ("only the one-dimensional marginal laws were
  used", line 469). For the top coordinates the Gaussian scaling step is replaced by pointwise
  scaling `g ↦ √(a/a_i) g` (which can only decrease `min{g², 3a}`). It is applied to
  `x = R^{1/2} ε` with `ε` uniform on `{±1}^d` (Rademacher sums satisfy `E g⁴ ≤ 3 (E g²)²`), so no
  Gaussian measure is needed.
* `tailSum k a = min_{|S| ≤ k} ∑_{i ∉ S} a_i` is the paper's `∑_{i > k} a_(i)` (decreasing order).
* `linearization`: Theorem `thm:linearization` in Rayleigh form.
* `certificate`: Proposition `prop:certificate` with `ε² = 1/9`, `λ² = 121/45000`, so
  `u = 8/27`, `v = 120000/121`.

## Proof structure

* `truncation` (lines 443–470): pointwise `d_m(z)² ≥ ∑_i min{z_i², T} - mT`
  (`Lin.sum_min_sub_le_distSparseSq`), the one-coordinate bound
  `E min{g_i², 3t} ≥ (3/4) min{E g_i², t}` (`Lin.coord_trunc_bound`), and the choice of the
  threshold `t = a_(4m+1)` (`Lin.tail_select`), for which `∑_i min{a_i, t} - 4m t` is the tail sum.
* `linearization_dual` (eq. (12), lines 488–493), for every `R ⪰ 0` (no trace normalization is
  needed): with `B = R^{1/2}` (`CFC.sqrt`) and `x = B ε`, `E x xᵀ = R`
  (`Lin.rad_mulVec_cross`), the coordinates of `V x` are Rademacher sums
  (`Lin.rad_mulVec_fourth`), so `truncation` and the hypothesis give
  `min_{|S| ≤ 4m} ∑_{i ∉ S} v_iᵀ R v_i ≤ (4/3) tr(H R)`.
* `linearization` (lines 495–543): the separation step is `common_coordinate_selection`
  (`SparseStack/Lin/Selection.lean`), applied with `j = 4m` and `(4/3) H`.
* `certificate` (lines 561–569): homogeneity, then `linearization` with
  `H = (1/9) I + λ⁻² XᵀX`.
-/

namespace SparseStack

open SparseFock

/-- `tailSum k a = min_{|S| ≤ k} ∑_{i ∉ S} a_i`, i.e. the sum of all but the `k` largest entries. -/
noncomputable def tailSum {n : ℕ} (k : ℕ) (a : Fin n → ℝ) : ℝ :=
  ⨅ S : {S : Finset (Fin n) // S.card ≤ k}, ∑ i ∈ (S.1)ᶜ, a i

/-- Lemma `lem:gaussian-truncation` (moment form): `E d_m(g)² ≥ (3/4) ∑_{i > 4m} a_(i)`. -/
theorem truncation {Ω : Type} [Fintype Ω] (μ : FiniteLaw Ω) {n : ℕ} (m : ℕ)
    (g : Ω → Fin n → ℝ)
    (h4 : ∀ i, μ.expect (fun ω => g ω i ^ 4) ≤ 3 * (μ.expect (fun ω => g ω i ^ 2)) ^ 2) :
    3 / 4 * tailSum (4 * m) (fun i => μ.expect (fun ω => g ω i ^ 2)) ≤
      μ.expect (fun ω => distSparseSq m (g ω)) := by
  have ha : ∀ i, 0 ≤ μ.expect (fun ω => g ω i ^ 2) :=
    fun i => μ.expect_nonneg (fun ω => sq_nonneg _)
  -- the threshold `t = a_(4m+1)`
  obtain ⟨t, ht0, hsel⟩ := Lin.tail_select (fun i => μ.expect (fun ω => g ω i ^ 2)) ha (4 * m)
  -- one coordinate at a time
  have hcoord : ∀ i, 3 / 4 * min (μ.expect (fun ω => g ω i ^ 2)) t ≤
      μ.expect (fun ω => min (g ω i ^ 2) (3 * t)) :=
    fun i => Lin.coord_trunc_bound μ (fun ω => g ω i) (h4 i) ht0
  -- the pointwise bound with `T = 3t`, in expectation
  have hpt : ∀ ω, ∑ i, min (g ω i ^ 2) (3 * t) - m * (3 * t) ≤ distSparseSq m (g ω) :=
    fun ω => Lin.sum_min_sub_le_distSparseSq m (g ω) (by positivity)
  have hE := μ.expect_mono hpt
  rw [FiniteLaw.expect_sub, Lin.expect_finset_sum, FiniteLaw.expect_const] at hE
  have hsum : ∑ i, 3 / 4 * min (μ.expect (fun ω => g ω i ^ 2)) t ≤
      ∑ i, μ.expect (fun ω => min (g ω i ^ 2) (3 * t)) :=
    Finset.sum_le_sum (fun i _ => hcoord i)
  rw [← Finset.mul_sum] at hsum
  have htail : tailSum (4 * m) (fun i => μ.expect (fun ω => g ω i ^ 2)) ≤
      ∑ i, min (μ.expect (fun ω => g ω i ^ 2)) t - ((4 * m : ℕ) : ℝ) * t := hsel
  push_cast at htail
  -- `(3/4) (∑_i min{a_i, t} - 4m t) = (3/4) ∑_i min{a_i, t} - 3m t`
  linarith

open scoped MatrixOrder in
/-- Eq. (12) of the paper, for every `R ⪰ 0` (the trace normalization is not needed): some `S`,
`|S| ≤ 4m`, has `∑_{i ∉ S} v_iᵀ R v_i ≤ tr(R ((4/3) H))`. Proof: `x = R^{1/2} ε` with `ε` uniform
on `{±1}^d` has `E x xᵀ = R`, and the coordinates of `V x` are Rademacher sums. -/
theorem linearization_dual {n d m : ℕ} (V : Matrix (Fin n) (Fin d) ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.PosSemidef)
    (hyp : ∀ x, distSparseSq m (V.mulVec x) ≤ dotProduct x (H.mulVec x))
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef) :
    ∃ S : Finset (Fin n), S.card ≤ 4 * m ∧
      ∑ i ∈ Sᶜ, dotProduct (V i) (R.mulVec (V i)) ≤ (R * ((4 / 3 : ℝ) • H)).trace := by
  -- the symmetric square root `B = R^{1/2}`
  obtain ⟨B, hBB, hBsym⟩ : ∃ B : Matrix (Fin d) (Fin d) ℝ, B * B = R ∧ ∀ a b, B a b = B b a := by
    refine ⟨CFC.sqrt R, CFC.sqrt_mul_sqrt_self R hR.nonneg, fun a b => ?_⟩
    have h := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg R)).isHermitian.eq
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    have h' := congrFun (congrFun h b) a
    simpa [Matrix.transpose_apply] using h'
  -- `H` is symmetric
  have hHsym : ∀ a b, H b a = H a b := by
    intro a b
    have h := hH.isHermitian.eq
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    have h' := congrFun (congrFun h a) b
    simpa [Matrix.transpose_apply] using h'
  -- second moments of `x = B ε`: `E x_a x_b = R_ab`
  have hx2 : ∀ a b, (Lin.radLaw d).expect
      (fun ε => (B.mulVec (Lin.sgnVec ε)) a * (B.mulVec (Lin.sgnVec ε)) b) = R a b := by
    intro a b
    rw [Lin.rad_mulVec_cross, ← hBB, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun p _ => by rw [Matrix.transpose_apply, hBsym b p])
  -- expectations of products of linear forms in `x`
  have hquad : ∀ u w : Fin d → ℝ, (Lin.radLaw d).expect (fun ε =>
      dotProduct u (B.mulVec (Lin.sgnVec ε)) * dotProduct w (B.mulVec (Lin.sgnVec ε))) =
      ∑ a, ∑ b, u a * w b * R a b := by
    intro u w
    have hexp : ∀ ε : Fin d → Bool,
        dotProduct u (B.mulVec (Lin.sgnVec ε)) * dotProduct w (B.mulVec (Lin.sgnVec ε)) =
        ∑ a, ∑ b, (u a * w b) * ((B.mulVec (Lin.sgnVec ε)) a * (B.mulVec (Lin.sgnVec ε)) b) := by
      intro ε
      generalize B.mulVec (Lin.sgnVec ε) = y
      simp only [dotProduct]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
    rw [FiniteLaw.expect_congr _ hexp, Lin.expect_finset_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Lin.expect_finset_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [FiniteLaw.expect_smul, hx2]
  -- the coordinates of `V x = (V B) ε` are Rademacher sums
  have h4 : ∀ i, (Lin.radLaw d).expect (fun ε => (V.mulVec (B.mulVec (Lin.sgnVec ε))) i ^ 4) ≤
      3 * ((Lin.radLaw d).expect (fun ε => (V.mulVec (B.mulVec (Lin.sgnVec ε))) i ^ 2)) ^ 2 := by
    intro i
    simp only [Matrix.mulVec_mulVec]
    exact Lin.rad_mulVec_fourth (V * B) i
  -- truncation
  have htr : 3 / 4 * tailSum (4 * m)
      (fun i => (Lin.radLaw d).expect (fun ε => (V.mulVec (B.mulVec (Lin.sgnVec ε))) i ^ 2)) ≤
      (Lin.radLaw d).expect (fun ε => distSparseSq m (V.mulVec (B.mulVec (Lin.sgnVec ε)))) :=
    truncation (Lin.radLaw d) m (fun ε => V.mulVec (B.mulVec (Lin.sgnVec ε))) h4
  -- the hypothesis, in expectation
  have hmono : (Lin.radLaw d).expect
      (fun ε => distSparseSq m (V.mulVec (B.mulVec (Lin.sgnVec ε)))) ≤
      (Lin.radLaw d).expect (fun ε =>
        dotProduct (B.mulVec (Lin.sgnVec ε)) (H.mulVec (B.mulVec (Lin.sgnVec ε)))) :=
    FiniteLaw.expect_mono _ (fun ε => hyp _)
  -- `E (V x)_i² = v_iᵀ R v_i`
  have hEg2 : ∀ i, (Lin.radLaw d).expect
      (fun ε => (V.mulVec (B.mulVec (Lin.sgnVec ε))) i ^ 2) =
      dotProduct (V i) (R.mulVec (V i)) := by
    intro i
    have hrw : ∀ ε : Fin d → Bool, (V.mulVec (B.mulVec (Lin.sgnVec ε))) i ^ 2 =
        dotProduct (V i) (B.mulVec (Lin.sgnVec ε)) *
          dotProduct (V i) (B.mulVec (Lin.sgnVec ε)) := by
      intro ε
      rw [sq]
      rfl
    rw [FiniteLaw.expect_congr _ hrw, hquad]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  -- `E xᵀ H x = ∑_{a,b} H_ab R_ab`
  have hEH : (Lin.radLaw d).expect (fun ε =>
      dotProduct (B.mulVec (Lin.sgnVec ε)) (H.mulVec (B.mulVec (Lin.sgnVec ε)))) =
      ∑ a, ∑ b, H a b * R a b := by
    have hexp : ∀ ε : Fin d → Bool,
        dotProduct (B.mulVec (Lin.sgnVec ε)) (H.mulVec (B.mulVec (Lin.sgnVec ε))) =
        ∑ a, ∑ b, H a b * ((B.mulVec (Lin.sgnVec ε)) a * (B.mulVec (Lin.sgnVec ε)) b) := by
      intro ε
      generalize B.mulVec (Lin.sgnVec ε) = y
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
    rw [FiniteLaw.expect_congr _ hexp, Lin.expect_finset_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Lin.expect_finset_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [FiniteLaw.expect_smul, hx2]
  -- `tr(R ((4/3) H)) = (4/3) ∑_{a,b} H_ab R_ab`
  have htrace : (R * ((4 / 3 : ℝ) • H)).trace = 4 / 3 * ∑ a, ∑ b, H a b * R a b := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
      rw [hHsym a b]
      ring))
  -- the minimizing set of the tail sum
  have hne := Lin.nonempty_cardLe n (4 * m)
  obtain ⟨⟨S, hS⟩, hSeq⟩ := exists_eq_ciInf_of_finite
    (f := fun S : {S : Finset (Fin n) // S.card ≤ 4 * m} =>
      ∑ i ∈ (S.1)ᶜ, (Lin.radLaw d).expect (fun ε => (V.mulVec (B.mulVec (Lin.sgnVec ε))) i ^ 2))
  refine ⟨S, hS, ?_⟩
  have htail : tailSum (4 * m)
      (fun i => (Lin.radLaw d).expect (fun ε => (V.mulVec (B.mulVec (Lin.sgnVec ε))) i ^ 2)) =
      ∑ i ∈ Sᶜ, (Lin.radLaw d).expect (fun ε => (V.mulVec (B.mulVec (Lin.sgnVec ε))) i ^ 2) :=
    hSeq.symm
  have hsumeq : ∑ i ∈ Sᶜ, dotProduct (V i) (R.mulVec (V i)) =
      ∑ i ∈ Sᶜ, (Lin.radLaw d).expect (fun ε => (V.mulVec (B.mulVec (Lin.sgnVec ε))) i ^ 2) :=
    Finset.sum_congr rfl (fun i _ => (hEg2 i).symm)
  rw [hsumeq, ← htail, htrace]
  rw [hEH] at hmono
  linarith

/-- Theorem `thm:linearization` (Rayleigh form): if `d_m(Vx)² ≤ xᵀHx` for all `x` with `H ⪰ 0`,
`m ≥ 1`, then some `I` with `|I| ≤ 8m` has `∑_{i ∉ I} (Vx)_i² ≤ (8/3) xᵀHx` for all `x`. -/
theorem linearization {n d m : ℕ} (hm : 1 ≤ m) (V : Matrix (Fin n) (Fin d) ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.PosSemidef)
    (hyp : ∀ x, distSparseSq m (V.mulVec x) ≤ dotProduct x (H.mulVec x)) :
    ∃ I : Finset (Fin n), I.card ≤ 8 * m ∧
      ∀ x, ∑ i ∈ Iᶜ, (V.mulVec x i) ^ 2 ≤ 8 / 3 * dotProduct x (H.mulVec x) := by
  have hH' : ((4 / 3 : ℝ) • H).PosSemidef := hH.smul (by norm_num)
  obtain ⟨I, hIcard, hI⟩ := common_coordinate_selection (j := 4 * m) V ((4 / 3 : ℝ) • H) hH'
    (fun R hR _ => linearization_dual V H hH hyp R hR)
  refine ⟨I, by omega, fun x => ?_⟩
  have hx := hI x
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hx
  linarith

/-- Proposition `prop:certificate` with `ε² = 1/9` and `λ² = 121/45000`. -/
theorem certificate {n r m : ℕ} {k : Type} [Fintype k] (hm : 1 ≤ m)
    (Q : Matrix (Fin n) (Fin r) ℝ) (hQ : Q.transpose * Q = 1) (X : Matrix k (Fin r) ℝ)
    (hyp : ∀ x, sqNorm x = 1 → 1 / 9 ≤ distSparseSq m (Q.mulVec x) →
      lambdaSq ≤ sqNorm (X.mulVec x)) :
    ∃ I : Finset (Fin n), I.card ≤ 8 * m ∧
      ∀ x, ∑ i ∈ Iᶜ, (Q.mulVec x i) ^ 2 ≤ uCert * sqNorm x + vCert * sqNorm (X.mulVec x) := by
  have hl : (0 : ℝ) < lambdaSq := by
    unfold lambdaSq
    norm_num
  -- homogeneous form (paper, lines 562–567): `d_m(Qx)² ≤ ε²‖x‖² + λ⁻²‖Xx‖²`
  have hhom : ∀ x, distSparseSq m (Q.mulVec x) ≤
      1 / 9 * sqNorm x + lambdaSq⁻¹ * sqNorm (X.mulVec x) := by
    intro x
    have hN : 0 ≤ sqNorm (X.mulVec x) := Lin.sqNorm_nonneg_aux _
    have hlN : 0 ≤ lambdaSq⁻¹ * sqNorm (X.mulVec x) := mul_nonneg (inv_nonneg.mpr hl.le) hN
    rcases (Lin.sqNorm_nonneg_aux x).eq_or_lt with h0 | hpos
    · have h := Lin.distSparseSq_le_sqNorm_aux m (Q.mulVec x)
      rw [Lin.sqNorm_mulVec_of_isometry Q hQ x, ← h0] at h
      rw [← h0]
      linarith
    · -- normalize: `y = c x` with `c = ‖x‖⁻¹`
      obtain ⟨c, hc⟩ : ∃ c : ℝ, (Real.sqrt (sqNorm x))⁻¹ = c := ⟨_, rfl⟩
      have hc2 : c ^ 2 * sqNorm x = 1 := by
        rw [← hc, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
      have hc2pos : 0 < c ^ 2 := by
        rw [← hc]
        have : 0 < Real.sqrt (sqNorm x) := Real.sqrt_pos.mpr hpos
        positivity
      have hy : sqNorm (c • x) = 1 := by
        rw [Lin.sqNorm_smul_aux, hc2]
      have hdy : distSparseSq m (Q.mulVec (c • x)) = c ^ 2 * distSparseSq m (Q.mulVec x) := by
        rw [Matrix.mulVec_smul, Lin.distSparseSq_smul_aux]
      have hXy : sqNorm (X.mulVec (c • x)) = c ^ 2 * sqNorm (X.mulVec x) := by
        rw [Matrix.mulVec_smul, Lin.sqNorm_smul_aux]
      by_cases hbig : 1 / 9 ≤ distSparseSq m (Q.mulVec (c • x))
      · -- `‖X y‖ ≥ λ` and `d_m(Q y)² ≤ ‖y‖² = 1`
        have hly := hyp (c • x) hy hbig
        rw [hXy] at hly
        have hd1 : distSparseSq m (Q.mulVec (c • x)) ≤ 1 := by
          have h := Lin.distSparseSq_le_sqNorm_aux m (Q.mulVec (c • x))
          rwa [Lin.sqNorm_mulVec_of_isometry Q hQ, hy] at h
        rw [hdy] at hd1
        have hkey : lambdaSq * distSparseSq m (Q.mulVec x) ≤ sqNorm (X.mulVec x) := by
          have hmul := mul_le_mul_of_nonneg_left hd1 hl.le
          have h1 : c ^ 2 * (lambdaSq * distSparseSq m (Q.mulVec x)) ≤
              c ^ 2 * sqNorm (X.mulVec x) := by
            nlinarith [hmul, hly]
          exact le_of_mul_le_mul_left h1 hc2pos
        have hD : distSparseSq m (Q.mulVec x) ≤ lambdaSq⁻¹ * sqNorm (X.mulVec x) := by
          rw [inv_mul_eq_div, le_div_iff₀ hl]
          linarith
        have hP : 0 ≤ 1 / 9 * sqNorm x := by positivity
        linarith
      · -- `d_m(Q y)² < 1/9`, i.e. `d_m(Q x)² < ‖x‖²/9`
        push Not at hbig
        rw [hdy] at hbig
        have hDP : distSparseSq m (Q.mulVec x) =
            (c ^ 2 * distSparseSq m (Q.mulVec x)) * sqNorm x := by
          calc distSparseSq m (Q.mulVec x)
              = distSparseSq m (Q.mulVec x) * (c ^ 2 * sqNorm x) := by rw [hc2, mul_one]
            _ = (c ^ 2 * distSparseSq m (Q.mulVec x)) * sqNorm x := by ring
        have hsm : (c ^ 2 * distSparseSq m (Q.mulVec x)) * sqNorm x ≤ 1 / 9 * sqNorm x :=
          mul_le_mul_of_nonneg_right hbig.le hpos.le
        linarith
  -- `H = (1/9) I + λ⁻² XᵀX ⪰ 0`
  obtain ⟨H, hHdef⟩ : ∃ H : Matrix (Fin r) (Fin r) ℝ,
      H = (1 / 9 : ℝ) • (1 : Matrix (Fin r) (Fin r) ℝ) + lambdaSq⁻¹ • (X.transpose * X) :=
    ⟨_, rfl⟩
  have hHpsd : H.PosSemidef := by
    have h1 : ((1 / 9 : ℝ) • (1 : Matrix (Fin r) (Fin r) ℝ)).PosSemidef :=
      Matrix.PosSemidef.one.smul (by norm_num)
    have h2 : (X.transpose * X).PosSemidef := by
      have h := Matrix.posSemidef_conjTranspose_mul_self X
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [hHdef]
    exact h1.add (h2.smul (inv_nonneg.mpr hl.le))
  have hHx : ∀ x : Fin r → ℝ,
      dotProduct x (H.mulVec x) = 1 / 9 * sqNorm x + lambdaSq⁻¹ * sqNorm (X.mulVec x) := by
    intro x
    have hXX : dotProduct x ((X.transpose * X).mulVec x) = sqNorm (X.mulVec x) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      rfl
    rw [hHdef, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hXX]
    rfl
  have hlin : ∀ x, distSparseSq m (Q.mulVec x) ≤ dotProduct x (H.mulVec x) := by
    intro x
    rw [hHx]
    exact hhom x
  obtain ⟨I, hI, hIx⟩ := linearization hm Q H hHpsd hlin
  refine ⟨I, hI, fun x => ?_⟩
  have h := hIx x
  rw [hHx] at h
  have hu : uCert = 8 / 3 * (1 / 9) := by
    unfold uCert
    norm_num
  have hv : vCert = 8 / 3 * lambdaSq⁻¹ := by
    unfold vCert lambdaSq
    norm_num
  rw [hu, hv]
  linarith

end SparseStack
