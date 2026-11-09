import SparseStack.Basic.Defs
import SparseStack.Loc.Basic
import SparseStack.Loc.LatticeCount
import SparseStack.Loc.RoundingAvg

/-!
# `d_m`, top-`m` removal and unbiased lattice rounding (paper, lines 299–349, 404–411)

Proof notes (W-LOC). Helpers are in `SparseStack/Loc/{Basic,LatticeCount,RoundingAvg}.lean`.
* `d_m`: the minimum over `|I| ≤ m` is attained (`Loc.exists_distSparseSq_eq`); the Lipschitz
  bound is Minkowski on `Iᶜ` for a minimizer `I` of `y`.
* Top-`m` removal: for a minimizer `I`, `h = w|_I`, `z = w|_{Iᶜ}/a`; the exchange argument
  (`Loc.topm_key`) gives `m w_i² ≤ ‖w‖²` for `i ∉ I`.
* `lattice_net`: `h = η/√r`, `N = hℤ^r ∩ (1+η)B`; rounding by `Loc.exists_round`; the count is the
  measure-free `Loc.card_netIdx_le` with `s = η/(1+η)`: `|N| ≤ (e (2+3η)/η)^r ≤ (16/η)^r`.
-/

namespace SparseStack

/-- `d_m(z)² ≤ ‖z‖²` (take `I = ∅`). -/
theorem distSparseSq_le_sqNorm (m : ℕ) {n : ℕ} (z : Fin n → ℝ) :
    distSparseSq m z ≤ sqNorm z := by
  refine (Loc.distSparseSq_le_of_card m z ∅ (by simp)).trans ?_
  rw [Loc.sqNorm_eq_sum_sq, Finset.compl_empty]

/-- `d_m(z)² ≥ 0`. -/
theorem distSparseSq_nonneg (m : ℕ) {n : ℕ} (z : Fin n → ℝ) : 0 ≤ distSparseSq m z := by
  obtain ⟨I, _, hI⟩ := Loc.exists_distSparseSq_eq m z
  rw [hI]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- `d_m` is `1`-Lipschitz (paper, line 305): `d_m(x) ≤ d_m(y) + ‖x - y‖`. -/
theorem sqrt_distSparseSq_le (m : ℕ) {n : ℕ} (x y : Fin n → ℝ) :
    Real.sqrt (distSparseSq m x) ≤ Real.sqrt (distSparseSq m y) + Real.sqrt (sqNorm (x - y)) := by
  obtain ⟨I, hI, hy⟩ := Loc.exists_distSparseSq_eq m y
  calc Real.sqrt (distSparseSq m x) ≤ Real.sqrt (∑ i ∈ Iᶜ, x i ^ 2) :=
        Real.sqrt_le_sqrt (Loc.distSparseSq_le_of_card m x I hI)
    _ = Real.sqrt (∑ i ∈ Iᶜ, (y i + (x - y) i) ^ 2) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        simp
    _ ≤ Real.sqrt (∑ i ∈ Iᶜ, y i ^ 2) + Real.sqrt (∑ i ∈ Iᶜ, (x - y) i ^ 2) :=
        Loc.sqrt_sum_sq_add_le _ _ _
    _ ≤ Real.sqrt (distSparseSq m y) + Real.sqrt (sqNorm (x - y)) := by
        rw [hy]
        gcongr
        rw [Loc.sqNorm_eq_sum_sq]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => sq_nonneg _)

/-- `d_m(c z)² = c² d_m(z)²`. -/
theorem distSparseSq_smul (m : ℕ) {n : ℕ} (c : ℝ) (z : Fin n → ℝ) :
    distSparseSq m (c • z) = c ^ 2 * distSparseSq m z := by
  unfold distSparseSq
  rw [Real.mul_iInf_of_nonneg (sq_nonneg c)]
  congr 1
  funext I
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Top-`m` removal (paper, lines 404–410): if `d_m(w) > 0`, then `w = h + a z` with `a = d_m(w)`,
disjoint supports, `‖z‖ = 1` and `m a² z_i² ≤ ‖w‖²` for all `i`. -/
theorem topm_decomposition (m : ℕ) {n : ℕ} (w : Fin n → ℝ) (hpos : 0 < distSparseSq m w) :
    ∃ h z : Fin n → ℝ, w = h + Real.sqrt (distSparseSq m w) • z ∧ (∀ i, h i = 0 ∨ z i = 0) ∧
      sqNorm z = 1 ∧ ∀ i, (m : ℝ) * distSparseSq m w * z i ^ 2 ≤ sqNorm w := by
  obtain ⟨I, hI, hmin⟩ := Loc.exists_distSparseSq_eq m w
  have hmax : ∀ J : Finset (Fin n), J.card ≤ m → ∑ j ∈ J, w j ^ 2 ≤ ∑ j ∈ I, w j ^ 2 := by
    intro J hJ
    have h1 := Loc.distSparseSq_le_of_card m w J hJ
    have h2 := Finset.sum_compl_add_sum I (fun j => w j ^ 2)
    have h3 := Finset.sum_compl_add_sum J (fun j => w j ^ 2)
    linarith
  generalize hd : distSparseSq m w = d at hpos hmin ⊢
  have ha0 : 0 < Real.sqrt d := Real.sqrt_pos.mpr hpos
  have ha2 : Real.sqrt d ^ 2 = d := Real.sq_sqrt hpos.le
  have hd0 : d ≠ 0 := hpos.ne'
  refine ⟨fun i => if i ∈ I then w i else 0, fun i => if i ∈ I then 0 else w i / Real.sqrt d,
    ?_, ?_, ?_, ?_⟩
  · funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · ring
    · rw [mul_div_cancel₀ _ ha0.ne']
      ring
  · intro i
    by_cases hi : i ∈ I
    · right
      simp [hi]
    · left
      simp [hi]
  · rw [Loc.sqNorm_eq_sum_sq]
    have hsplit : ∑ i, (if i ∈ I then (0 : ℝ) else w i / Real.sqrt d) ^ 2 =
        ∑ i ∈ Iᶜ, (w i / Real.sqrt d) ^ 2 := by
      rw [← Finset.sum_compl_add_sum I]
      have hI0 : ∑ i ∈ I, (if i ∈ I then (0 : ℝ) else w i / Real.sqrt d) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp [hi]
      rw [hI0, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_compl] at hi
      simp [hi]
    rw [hsplit]
    simp_rw [div_pow]
    rw [← Finset.sum_div, ← hmin, ha2]
    exact div_self hd0
  · intro i
    by_cases hi : i ∈ I
    · simp only [hi, if_true]
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, mul_zero]
      exact Loc.sqNorm_nonneg w
    · simp only [hi, if_false]
      rw [Loc.sqNorm_eq_sum_sq]
      calc (m : ℝ) * d * (w i / Real.sqrt d) ^ 2 = (m : ℝ) * w i ^ 2 * (d / d) := by
            rw [div_pow, ha2]
            ring
        _ = (m : ℝ) * w i ^ 2 := by rw [div_self hd0, mul_one]
        _ ≤ ∑ j, w j ^ 2 := Loc.topm_key w I hI hmax i hi

/-- Lemma `lem:rounding` (paper, lines 308–349): for `0 < η < 1` there is a finite set
`N ⊂ (1+η) B₂^r` with `|N| ≤ (16/η)^r` such that every unit `x` and every real matrix `T` with `r`
columns admit `y ∈ N` with `‖x - y‖ ≤ η` and `‖T(x - y)‖² ≤ (η²/(4r)) ‖T‖_F²`. -/
theorem lattice_net (r : ℕ) (hr : 1 ≤ r) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ N : Finset (Fin r → ℝ), (N.card : ℝ) ≤ (16 / η) ^ r ∧
      (∀ y ∈ N, sqNorm y ≤ (1 + η) ^ 2) ∧
      ∀ (k : Type) [Fintype k] (T : Matrix k (Fin r) ℝ) (x : Fin r → ℝ), sqNorm x = 1 →
        ∃ y ∈ N, sqNorm (x - y) ≤ η ^ 2 ∧
          sqNorm (T.mulVec (x - y)) ≤ η ^ 2 / (4 * r) * frobSq T := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hsr : 0 < √(r : ℝ) := Real.sqrt_pos.mpr hr0
  have hsr2 : √(r : ℝ) * √(r : ℝ) = r := Real.mul_self_sqrt hr0.le
  have hη' : η ≠ 0 := hη0.ne'
  have h1η : (1 + η) ≠ 0 := by linarith
  obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = η / √(r : ℝ) := ⟨_, rfl⟩
  have hh : 0 < h := by rw [hh_def]; exact div_pos hη0 hsr
  have hh2 : h ^ 2 = η ^ 2 / r := by
    rw [hh_def, div_pow, Real.sq_sqrt hr0.le]
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈(1 + η) / h⌉₊ := ⟨_, rfl⟩
  refine ⟨(Loc.netIdx r h (1 + η) K).image (fun v i => h * (v i : ℝ)), ?_, ?_, ?_⟩
  · -- cardinality
    have hs : 0 < η / (1 + η) := div_pos hη0 (by linarith)
    have hcount := Loc.card_netIdx_le r hh (by linarith : (0 : ℝ) ≤ 1 + η) K hs
    have hL : √(r : ℝ) * (1 + η) / h = r * (1 + η) / η := by
      rw [hh_def, div_div_eq_mul_div, mul_right_comm, hsr2]
    have hsL : η / (1 + η) * (√(r : ℝ) * (1 + η) / h) = r := by
      rw [hL]
      field_simp
    have h2s : 1 + 2 / (η / (1 + η)) = (2 + 3 * η) / η := by
      rw [div_div_eq_mul_div]
      field_simp
      ring
    rw [hsL, h2s] at hcount
    have hexp : Real.exp (r : ℝ) = Real.exp 1 ^ r := by
      rw [← Real.exp_nat_mul, mul_one]
    rw [hexp, ← mul_pow] at hcount
    have hbase : Real.exp 1 * ((2 + 3 * η) / η) ≤ 16 / η := by
      have he := Real.exp_one_lt_d9
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hη0]
      nlinarith [Real.exp_pos 1, mul_pos (sub_pos.mpr hη1) (Real.exp_pos 1)]
    calc (((Loc.netIdx r h (1 + η) K).image (fun v i => h * (v i : ℝ))).card : ℝ)
        ≤ (Loc.netIdx r h (1 + η) K).card := by exact_mod_cast Finset.card_image_le
      _ ≤ (Real.exp 1 * ((2 + 3 * η) / η)) ^ r := hcount
      _ ≤ (16 / η) ^ r := pow_le_pow_left₀ (by positivity) hbase r
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    unfold Loc.netIdx at hv
    exact (Finset.mem_filter.mp hv).2
  · intro k _ T x hx
    obtain ⟨v, hv1, hv2⟩ := Loc.exists_round T hh x
    have hxy : sqNorm (x - fun i => h * (v i : ℝ)) ≤ η ^ 2 := by
      rw [Loc.sqNorm_eq_sum_sq]
      calc ∑ i, (x - fun i => h * (v i : ℝ)) i ^ 2 ≤ ∑ _i : Fin r, h ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have hi := abs_le.mp (hv1 i)
            simp only [Pi.sub_apply]
            exact sq_le_sq' hi.1 hi.2
        _ = η ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hh2]
            field_simp
    have hy : sqNorm (fun i => h * (v i : ℝ)) ≤ (1 + η) ^ 2 := by
      have h1 := Loc.sqrt_sqNorm_sub_le x (x - fun i => h * (v i : ℝ))
      rw [sub_sub_cancel, hx, Real.sqrt_one] at h1
      have h2 : √(sqNorm (x - fun i => h * (v i : ℝ))) ≤ η := by
        rw [Real.sqrt_le_left hη0.le]
        exact hxy
      have h3 : √(sqNorm (fun i => h * (v i : ℝ))) ≤ 1 + η := by linarith
      rwa [Real.sqrt_le_left (by linarith)] at h3
    have hvI : v ∈ Loc.netIdx r h (1 + η) K := by
      unfold Loc.netIdx
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => ?_, hy⟩
      have hyi : |h * (v i : ℝ)| ≤ 1 + η := by
        have h1 : (h * (v i : ℝ)) ^ 2 ≤ (1 + η) ^ 2 :=
          (Loc.sq_le_sqNorm (fun i => h * (v i : ℝ)) i).trans hy
        exact abs_le_of_sq_le_sq h1 (by linarith)
      have hvi : |(v i : ℝ)| ≤ (K : ℝ) := by
        have h2 : |(v i : ℝ)| * h ≤ 1 + η := by
          rw [abs_mul, abs_of_pos hh] at hyi
          linarith
        have h3 : |(v i : ℝ)| ≤ (1 + η) / h := by
          rw [le_div_iff₀ hh]
          exact h2
        rw [hK]
        exact h3.trans (Nat.le_ceil _)
      rw [Finset.mem_Icc]
      have h4 := abs_le.mp hvi
      constructor
      · exact_mod_cast h4.1
      · exact_mod_cast h4.2
    refine ⟨fun i => h * (v i : ℝ), Finset.mem_image.mpr ⟨v, hvI, rfl⟩, hxy, ?_⟩
    calc sqNorm (T.mulVec (x - fun i => h * (v i : ℝ)))
        = sqNorm (T.mulVec (fun i => x i - h * (v i : ℝ))) := rfl
      _ ≤ h ^ 2 / 4 * frobSq T := hv2
      _ = η ^ 2 / (4 * r) * frobSq T := by
          rw [hh2]
          field_simp

end SparseStack
