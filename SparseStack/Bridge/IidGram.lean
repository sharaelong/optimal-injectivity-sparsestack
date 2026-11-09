import Mathlib
import SparseFockFormal.VacuumMoment
import SparseFockFormal.MatrixFrameBridge
import SparseStack.Bridge.FiniteLawAux

/-!
# Diagonal/hollow split of the iid Gram matrix (paper, Lemma `lem:iid-norm`, lines 586–590)

For the iid ternary configuration `x` on `m = a B` rows and the matrix `X_{ℓj} = η(x_{ℓj})/√B`,
and `W` with `WᵀW = I`:

* `rowDiag B W ω = Wᵀ diag(η(ω_j)²/B) W` (the row-`ℓ` diagonal part `P_ℓ`);
* `rowDiag_posSemidef`, `one_sub_rowDiag_posSemidef`: `0 ⪯ P_ℓ ⪯ I`;
* `rowDiag_mean`: `E P_ℓ = I/B` under the product law of one row;
* `gram_decomp`: `(XW)ᵀ(XW) = ∑_ℓ P_ℓ + a • F`, where `F` is Heidary's
  `VacuumMoment.iidGramError B (frameOfMatrix W hW) x` (normalization `(1/m) η η = (1/a) X X`);
* `iidGramError_isHermitian`: `F` is symmetric.
-/

namespace SparseStack.HeidBridge

open SparseFock ParsevalFrame

/-- `η(x)²/B ∈ {0, 1}`. -/
theorem eta_sq_div_eq {B : ℕ} (hB : 0 < B) (x : EtaOutcome) :
    TernaryJacobi.eta B x ^ 2 / B = if x = .zero then 0 else 1 := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hs : Real.sqrt (B : ℝ) ^ 2 = B := Real.sq_sqrt (Nat.cast_nonneg B)
  cases x <;> simp [TernaryJacobi.eta, hs, hB0]

theorem eta_sq_div_nonneg (B : ℕ) (x : EtaOutcome) : 0 ≤ TernaryJacobi.eta B x ^ 2 / B := by
  positivity

theorem eta_sq_div_le_one {B : ℕ} (hB : 0 < B) (x : EtaOutcome) :
    TernaryJacobi.eta B x ^ 2 / B ≤ 1 := by
  rw [eta_sq_div_eq hB]
  split_ifs <;> norm_num

/-- The row-`ℓ` diagonal part `P(ω) = Wᵀ diag(η(ω_j)²/B) W`. -/
noncomputable def rowDiag {n d : ℕ} (B : ℕ) (W : Matrix (Fin n) (Fin d) ℝ)
    (ω : Fin n → EtaOutcome) : Matrix (Fin d) (Fin d) ℝ :=
  W.transpose * Matrix.diagonal (fun j => TernaryJacobi.eta B (ω j) ^ 2 / B) * W

theorem rowDiag_apply {n d : ℕ} (B : ℕ) (W : Matrix (Fin n) (Fin d) ℝ)
    (ω : Fin n → EtaOutcome) (α γ : Fin d) :
    rowDiag B W ω α γ = ∑ j, W j α * W j γ * (TernaryJacobi.eta B (ω j) ^ 2 / B) := by
  rw [rowDiag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  ring

/-- `0 ⪯ P(ω)`. -/
theorem rowDiag_posSemidef {n d : ℕ} (B : ℕ) (W : Matrix (Fin n) (Fin d) ℝ)
    (ω : Fin n → EtaOutcome) : (rowDiag B W ω).PosSemidef := by
  have hdiag : (Matrix.diagonal (fun j => TernaryJacobi.eta B (ω j) ^ 2 / B)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun j => eta_sq_div_nonneg B (ω j))
  have h := hdiag.conjTranspose_mul_mul_same W
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- `P(ω) ⪯ I`. -/
theorem one_sub_rowDiag_posSemidef {n d : ℕ} {B : ℕ} (hB : 0 < B)
    (W : Matrix (Fin n) (Fin d) ℝ) (hW : W.transpose * W = 1) (ω : Fin n → EtaOutcome) :
    (1 - rowDiag B W ω).PosSemidef := by
  have hid : 1 - rowDiag B W ω = W.transpose *
      Matrix.diagonal (fun j => 1 - TernaryJacobi.eta B (ω j) ^ 2 / B) * W := by
    rw [rowDiag, ← Matrix.diagonal_sub (fun _ => (1 : ℝ)), Matrix.diagonal_one, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hW]
  have hdiag : (Matrix.diagonal (fun j => 1 - TernaryJacobi.eta B (ω j) ^ 2 / B)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun j => sub_nonneg.mpr (eta_sq_div_le_one hB (ω j)))
  have h := hdiag.conjTranspose_mul_mul_same W
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rwa [hid]

/-- `E P = I/B` under the product law of one row. -/
theorem rowDiag_mean {n d : ℕ} {B : ℕ} (hB : 0 < B) (W : Matrix (Fin n) (Fin d) ℝ)
    (hW : W.transpose * W = 1) :
    ∑ ω, (FiniteLaw.independentProduct
        (fun _ : Fin n => TernaryJacobi.law B hB)).weight ω • rowDiag B W ω =
      (1 / (B : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  ext α γ
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  change (FiniteLaw.independentProduct (fun _ : Fin n => TernaryJacobi.law B hB)).expect
      (fun ω => rowDiag B W ω α γ) = _
  simp only [rowDiag_apply]
  rw [expect_finset_sum]
  have hcoord : ∀ j : Fin n,
      (FiniteLaw.independentProduct (fun _ : Fin n => TernaryJacobi.law B hB)).expect
        (fun ω => W j α * W j γ * (TernaryJacobi.eta B (ω j) ^ 2 / B)) =
        W j α * W j γ * (1 / (B : ℝ)) := by
    intro j
    rw [FiniteLaw.expect_smul]
    have h := FiniteLaw.expect_independentProduct_apply
      (fun _ : Fin n => TernaryJacobi.law B hB) j (fun x => TernaryJacobi.eta B x ^ 2 / B)
    rw [h]
    have h2 : (TernaryJacobi.law B hB).expect (fun x => TernaryJacobi.eta B x ^ 2 / B) =
        (1 / (B : ℝ)) * (TernaryJacobi.law B hB).expect (fun x => TernaryJacobi.eta B x ^ 2) := by
      rw [← FiniteLaw.expect_smul]
      apply FiniteLaw.expect_congr
      intro x
      ring
    rw [h2, TernaryJacobi.law_expect_eta_sq hB, mul_one]
  simp only [hcoord]
  have hWW : ∑ j, W j α * W j γ = (1 : Matrix (Fin d) (Fin d) ℝ) α γ := by
    rw [← hW]
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  rw [← Finset.sum_mul, hWW]
  ring

/-- Swap the two indices of a hollow (off-diagonal) double sum. -/
theorem sum_erase_swap {n : ℕ} (g : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, g i j = ∑ i, ∑ j ∈ Finset.univ.erase i, g j i := by
  have h : ∀ (f : Fin n → Fin n → ℝ),
      ∑ i, ∑ j ∈ Finset.univ.erase i, f i j = ∑ i, ∑ j, f i j - ∑ i, f i i := by
    intro f
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  rw [h g, h (fun i j => g j i), Finset.sum_comm]

/-- Heidary's iid Gram error is symmetric. -/
theorem iidGramError_isHermitian {m n d : ℕ} (B : ℕ) (F : Frame n d)
    (x : ProductFock.Configuration m n) :
    (VacuumMoment.iidGramError B F x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro α γ
  rw [star_trivial, VacuumMoment.iidGramError_apply, VacuumMoment.iidGramError_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [sum_erase_swap]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The diagonal/hollow split `(XW)ᵀ(XW) = ∑_ℓ P_ℓ + a • F` (entries `X_{ℓj} = η/√B`). -/
theorem gram_decomp {a B n d : ℕ} (hB : 0 < B) (ha : 0 < a) (W : Matrix (Fin n) (Fin d) ℝ)
    (hW : W.transpose * W = 1) (x : ProductFock.Configuration (a * B) n)
    (X : Matrix (Fin (a * B)) (Fin n) ℝ)
    (hX : ∀ ℓ j, X ℓ j = TernaryJacobi.eta B (x (ℓ, j)) / Real.sqrt B) :
    (X * W).transpose * (X * W) =
      ∑ ℓ, rowDiag B W (fun j => x (ℓ, j)) +
        (a : ℝ) • VacuumMoment.iidGramError B (MatrixFrameBridge.frameOfMatrix W hW) x := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hsq : Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) = B := Real.mul_self_sqrt (Nat.cast_nonneg B)
  have hsqne : Real.sqrt (B : ℝ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsq
    exact hB0 hsq.symm
  have hm : (a : ℝ) * (1 / ((a * B : ℕ) : ℝ)) = 1 / B := by
    push_cast
    field_simp
  have key : ∀ u v : ℝ, u / Real.sqrt B * (v / Real.sqrt B) = u * v / B := by
    intro u v
    rw [div_mul_div_comm, hsq]
  ext α γ
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, VacuumMoment.iidGramError_apply,
    ← mul_assoc, hm, Matrix.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowDiag_apply,
    MatrixFrameBridge.frameOfMatrix_u, ProductFock.etaCoordinate]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [Finset.sum_mul_sum]
  have hsplit : ∀ j : Fin n,
      ∑ k, X ℓ j * W j α * (X ℓ k * W k γ) =
        X ℓ j * W j α * (X ℓ j * W j γ) +
          ∑ k ∈ Finset.univ.erase j, X ℓ j * W j α * (X ℓ k * W k γ) :=
    fun j => (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  simp only [hsplit]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    have h1 : X ℓ j * W j α * (X ℓ j * W j γ) = (X ℓ j * X ℓ j) * W j α * W j γ := by ring
    rw [h1, hX ℓ j, key]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have h1 : X ℓ j * W j α * (X ℓ k * W k γ) = (X ℓ j * X ℓ k) * W j α * W k γ := by ring
    rw [h1, hX ℓ j, hX ℓ k, key]
    ring

end SparseStack.HeidBridge
