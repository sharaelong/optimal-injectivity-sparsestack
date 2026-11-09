import SparseStack.External.Heidary
import SparseStack.MatrixConc.Chernoff
import SparseStack.Bridge.IidGram
import SparseStack.Bridge.IidNumerics

/-!
# Independent-entry norm estimate (paper, Lemma `lem:iid-norm`, refined form, lines 575–629, 830–846)

The iid ternary model is Heidary's `ProductFock.iidLaw B hB m n` (entries `η ∈ {±√B, 0}` with
probabilities `1/(2B), 1/(2B), 1 - 1/B`); our `X_{ℓj} = η_{ℓj}/√B ∈ {-1, 0, 1}` (`iidMatrix`).

Refined bound (used by the refined cross-Gram estimate, `p ≥ 64`):
`E‖XW‖² ≤ 46 (a + D_p/B + p)`, `D_p = d + 2p + 1`, `m = aB`.

Proof: `a⁻¹ (XW)ᵀ(XW) = D + F` (diagonal + hollow).
* Diagonal: `a D = ∑_ℓ P_ℓ`, `P_ℓ = Wᵀ diag(X_{ℓ·}²) W`, independent, `0 ⪯ P_ℓ ⪯ I`,
  `E P_ℓ = I/B`; `isotropic_matrix_chernoff` gives `a E‖D‖ ≤ (e-1) a + log d ≤ 1.7183 a + p`.
  (This replaces the paper's matrix Bernstein step `E‖D‖ ≤ 1 + √(2p/a) + p/(3a)`.)
* Hollow: `F = iidGramError` (Heidary), `‖F‖^{2p} ≤ tr F^{2p}`, eq. (83), `d^{1/(2p)} 3(3+√2) < 22`:
  `a E‖F‖ ≤ 22 (√(a D_p/B) + D_p/B + 2p + 1) ≤ 11 a + 33 D_p/B + 44 p + 22`.
* Total `≤ 12.72 a + 33 D_p/B + 45.34 p ≤ 46 (a + D_p/B + p)` (`p ≥ 64`).

Helper files: `SparseStack/Bridge/FiniteLawAux.lean` (Jensen, regrouping the product law by rows),
`SparseStack/Bridge/IidGram.lean` (the split `(XW)ᵀ(XW) = ∑_ℓ P_ℓ + a • F`, `0 ⪯ P_ℓ ⪯ I`,
`E P_ℓ = I/B`, symmetry of `F`), `SparseStack/Bridge/IidNumerics.lean` (scalar numerics).
-/

namespace SparseStack

open SparseFock
open scoped Matrix.Norms.L2Operator

/-- The iid ternary matrix `X_{ℓj} = η_{ℓj}/√B ∈ {-1, 0, 1}`. -/
noncomputable def iidMatrix {m n : ℕ} (B : ℕ) (x : ProductFock.Configuration m n) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun ℓ j => TernaryJacobi.eta B (x (ℓ, j)) / Real.sqrt B

/-- Pointwise split: `‖XW‖² = ‖(XW)ᵀ(XW)‖ ≤ ‖∑_ℓ P_ℓ‖ + a ‖F‖`. -/
theorem iidMatrix_sq_norm_le {a B n d : ℕ} (hB : 0 < B) (ha : 0 < a)
    (W : Matrix (Fin n) (Fin d) ℝ) (hW : W.transpose * W = 1)
    (x : ProductFock.Configuration (a * B) n) :
    ‖iidMatrix B x * W‖ ^ 2 ≤
      ‖∑ ℓ, HeidBridge.rowDiag B W (fun j => x (ℓ, j))‖ +
        (a : ℝ) * ‖VacuumMoment.iidGramError B (MatrixFrameBridge.frameOfMatrix W hW) x‖ := by
  have h1 : ‖iidMatrix B x * W‖ ^ 2 =
      ‖(iidMatrix B x * W).transpose * (iidMatrix B x * W)‖ := by
    rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [h1, HeidBridge.gram_decomp hB ha W hW x (iidMatrix B x) (fun ℓ j => rfl)]
  calc _ ≤ ‖∑ ℓ, HeidBridge.rowDiag B W (fun j => x (ℓ, j))‖ +
        ‖(a : ℝ) • VacuumMoment.iidGramError B (MatrixFrameBridge.frameOfMatrix W hW) x‖ :=
        norm_add_le _ _
    _ = _ := by rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg a)]

/-- Diagonal part (isotropic matrix Chernoff over the independent rows):
`E ‖∑_ℓ P_ℓ‖ ≤ (e - 1) a + log d`. -/
theorem iid_diag_bound {a B n d : ℕ} (hB : 1 < B) (ha : 0 < a) (hd : 0 < d)
    (W : Matrix (Fin n) (Fin d) ℝ) (hW : W.transpose * W = 1) :
    (ProductFock.iidLaw B hB (a * B) n).expect
        (fun x => ‖∑ ℓ, HeidBridge.rowDiag B W (fun j => x (ℓ, j))‖) ≤
      (Real.exp 1 - 1) * a + Real.log d := by
  have hB0 : 0 < B := by omega
  have hC := isotropic_matrix_chernoff (ι := Fin (a * B)) (Ω := Fin n → EtaOutcome) (d := d) hd
    (fun _ => FiniteLaw.independentProduct (fun _ : Fin n => TernaryJacobi.law B hB0))
    (fun _ => HeidBridge.rowDiag B W) (fun _ => 1 / (B : ℝ))
    (fun _ ω => HeidBridge.rowDiag_posSemidef B W ω)
    (fun _ ω => HeidBridge.one_sub_rowDiag_posSemidef hB0 W hW ω)
    (fun _ => HeidBridge.rowDiag_mean hB0 W hW)
  have hsum : ∑ _ℓ : Fin (a * B), (1 / (B : ℝ)) = a := by
    have hB0' : (B : ℝ) ≠ 0 := by exact_mod_cast hB0.ne'
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  rw [hsum] at hC
  rw [ProductFock.iidLaw, HeidBridge.expect_independentProduct_curry]
  exact hC

/-- Hollow part (Heidary eq. (83) and Lyapunov): `E ‖F‖ ≤ e^{1/2} · 3 β_p` with
`β_p = betaEnvelope d p (aB) a`, using `d ≤ e^p`. -/
theorem iid_hollow_bound {a B n d : ℕ} (hB : 1 < B) (ha : 0 < a)
    (W : Matrix (Fin n) (Fin d) ℝ) (hW : W.transpose * W = 1) (p : ℕ) (hp : 0 < p)
    (hdexp : (d : ℝ) ≤ Real.exp p) :
    (ProductFock.iidLaw B hB (a * B) n).expect
        (fun x => ‖VacuumMoment.iidGramError B (MatrixFrameBridge.frameOfMatrix W hW) x‖) ≤
      Real.exp (1 / 2) *
        (3 * PaperParameters.betaEnvelope d p ((a * B : ℕ) : ℝ) (a : ℝ)) := by
  set F := MatrixFrameBridge.frameOfMatrix W hW with hF
  set μ := ProductFock.iidLaw B hB (a * B) n with hμ
  set β := PaperParameters.betaEnvelope d p ((a * B : ℕ) : ℝ) (a : ℝ) with hβ
  have hm : (0 : ℝ) < ((a * B : ℕ) : ℝ) := by
    have : 0 < a * B := Nat.mul_pos ha (by omega)
    exact_mod_cast this
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hβ0 : 0 ≤ β := PaperParameters.betaEnvelope_nonneg hm haR
  have htr : μ.expect (fun x => ‖VacuumMoment.iidGramError B F x‖ ^ (2 * p)) ≤
      (d : ℝ) * (3 * β) ^ (2 * p) :=
    (FiniteLaw.expect_mono _ (fun x => MatrixTail.opNorm_even_pow_le_trace _
      (HeidBridge.iidGramError_isHermitian B F x) p hp)).trans
      (External.heidary_eq83_all_q (s := a) (b := B) (q := p) ha hB F)
  have hK : μ.expect (fun x => ‖VacuumMoment.iidGramError B F x‖ ^ (2 * p)) ≤
      (Real.exp (1 / 2) * (3 * β)) ^ (2 * p) := by
    calc _ ≤ (d : ℝ) * (3 * β) ^ (2 * p) := htr
      _ ≤ Real.exp p * (3 * β) ^ (2 * p) :=
        mul_le_mul_of_nonneg_right hdexp (by positivity)
      _ = (Real.exp (1 / 2) * (3 * β)) ^ (2 * p) := by
        rw [mul_pow (Real.exp (1 / 2)), ← Real.exp_nat_mul]
        congr 2
        push_cast
        ring
  exact HeidBridge.expect_le_of_expect_pow_le μ _ (fun x => norm_nonneg _) (by omega)
    (by positivity) hK

/-- Lemma `lem:iid-norm`, refined (`p ≥ 64`): `E‖XW‖² ≤ 46 (a + D_p/B + p)`. -/
theorem iid_norm_refined {a B n d : ℕ} (hB : 1 < B) (ha : 1 ≤ a)
    (W : Matrix (Fin n) (Fin d) ℝ) (hW : W.transpose * W = 1) (hd : 1 ≤ d) (p : ℕ)
    (hp : 64 ≤ p) (hplog : Real.log (2 * d) ≤ p) :
    (ProductFock.iidLaw B hB (a * B) n).expect (fun x => ‖iidMatrix B x * W‖ ^ 2) ≤
      46 * (a + ((d : ℝ) + 2 * p + 1) / B + p) := by
  have hB0 : 0 < B := by omega
  have ha0 : 0 < a := by omega
  have hp0 : 0 < p := by omega
  set F := MatrixFrameBridge.frameOfMatrix W hW with hF
  set μ := ProductFock.iidLaw B hB (a * B) n with hμ
  -- `log d ≤ p` and `d ≤ e^p`
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogd : Real.log d ≤ p := le_trans (Real.log_le_log hd0 (by linarith)) hplog
  have hdexp : (d : ℝ) ≤ Real.exp p := by
    calc (d : ℝ) = Real.exp (Real.log d) := (Real.exp_log hd0).symm
      _ ≤ Real.exp p := Real.exp_le_exp.2 hlogd
  -- the two parts
  have hD := iid_diag_bound hB ha0 (by omega) W hW
  have hFb := iid_hollow_bound hB ha0 W hW p hp0 hdexp
  have hE : μ.expect (fun x => ‖iidMatrix B x * W‖ ^ 2) ≤
      ((Real.exp 1 - 1) * a + Real.log d) +
        (a : ℝ) * (Real.exp (1 / 2) *
          (3 * PaperParameters.betaEnvelope d p ((a * B : ℕ) : ℝ) (a : ℝ))) := by
    calc _ ≤ μ.expect (fun x => ‖∑ ℓ, HeidBridge.rowDiag B W (fun j => x (ℓ, j))‖ +
          (a : ℝ) * ‖VacuumMoment.iidGramError B F x‖) :=
          FiniteLaw.expect_mono _ (fun x => iidMatrix_sq_norm_le hB0 ha0 W hW x)
      _ = μ.expect (fun x => ‖∑ ℓ, HeidBridge.rowDiag B W (fun j => x (ℓ, j))‖) +
          (a : ℝ) * μ.expect (fun x => ‖VacuumMoment.iidGramError B F x‖) := by
          rw [FiniteLaw.expect_add, FiniteLaw.expect_smul]
      _ ≤ _ := by
          gcongr
  -- numerics
  set Dq : ℝ := ((d + 2 * p + 1 : ℕ) : ℝ) with hDq
  set m : ℝ := ((a * B : ℕ) : ℝ) with hmdef
  set t : ℝ := Real.sqrt (Dq / m) with htdef
  set y : ℝ := Dq / B with hydef
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB0
  have hmeq : m = (a : ℝ) * B := by rw [hmdef]; push_cast; ring
  have hDq0 : 0 ≤ Dq := by rw [hDq]; positivity
  have hy0 : 0 ≤ y := by rw [hydef]; positivity
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hay : (a : ℝ) * (Dq / m) = y := by
    rw [hmeq, hydef]
    field_simp
  have hac : (a : ℝ) * (((2 * p + 1 : ℕ) : ℝ) / a) = 2 * p + 1 := by
    push_cast
    field_simp
  have hat2 : ((a : ℝ) * t) ^ 2 = a * y := by
    rw [mul_pow, htdef, Real.sq_sqrt (by rw [hmeq]; positivity), ← hay]
    ring
  have hat : (a : ℝ) * t ≤ (a + y) / 2 := HeidBridge.am_gm_half haR.le ht0 hy0 hat2
  have hβeq : (a : ℝ) * (Real.exp (1 / 2) *
      (3 * PaperParameters.betaEnvelope d p ((a * B : ℕ) : ℝ) (a : ℝ))) =
      (Real.exp (1 / 2) * (3 * (3 + Real.sqrt 2))) * (a * t + y + (2 * p + 1)) := by
    rw [External.betaEnvelope_eq, ← hay, ← hac]
    ring
  have hfin := HeidBridge.iid_final_numeric haR.le hy0 (by exact_mod_cast hp) hlogd ht0 hat
    HeidBridge.exp_half_mul_lt_22
  have hyeq : y = ((d : ℝ) + 2 * p + 1) / B := by
    rw [hydef, hDq]
    push_cast
    ring
  rw [hβeq] at hE
  rw [← hyeq]
  linarith

end SparseStack
