import SparseStack.Cross.MatrixNorm
import SparseStack.Cross.ProbLemmas

/-!
# Cross-Gram bound, step (6): padding the rows to `m = aB` (W-CROSS)

The `N` nonzero rows of `X_N` (rows in `I`) are embedded injectively into `Fin m` (`N ≤ m`); by the
selection identity they have the law of the corresponding rows of Heidary's `m × n` iid matrix,
and selecting rows cannot increase the operator norm (`l2_opNorm_rowSelect_le_one`).
-/

namespace SparseStack
namespace Cross

open SparseFock
open scoped Matrix.Norms.L2Operator

/-- An injection of `I` into `Fin m` when `|I| ≤ m`. -/
theorem exists_injOn_fin {n m : ℕ} (I : Finset (Fin n)) (h : I.card ≤ m) (hm : 0 < m) :
    ∃ f : Fin n → Fin m, Set.InjOn f I := by
  refine ⟨fun i => if hi : i ∈ I then Fin.castLE h (I.equivFin ⟨i, hi⟩) else ⟨0, hm⟩, ?_⟩
  intro i hi j hj hij
  have hi' : i ∈ I := hi
  have hj' : j ∈ I := hj
  simp only [dif_pos hi', dif_pos hj'] at hij
  have h1 := I.equivFin.injective (Fin.castLE_injective h hij)
  exact congrArg Subtype.val h1

/-- **Step (6)**: `E ‖X_N V‖ ≤ E ‖X_m V‖` (adding independent rows cannot decrease the operator
norm). -/
theorem pad_comparison {n d B m : ℕ} (hB : 1 < B) (I : Finset (Fin n)) (hIm : I.card ≤ m)
    (hm : 0 < m) (V : Matrix (Fin n) (Fin d) ℝ) :
    (ternLaw n B (Nat.zero_lt_of_lt hB)).expect (fun z => ‖ternMat B I z * V‖) ≤
      (ProductFock.iidLaw B hB m n).expect (fun x => ‖iidMat B x * V‖) := by
  obtain ⟨f, hf⟩ := exists_injOn_fin I hIm hm
  -- the row-selection matrix `P` (row `i ∈ I` picks row `f i`)
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin m) ℝ,
      P = Matrix.of fun i ℓ => if i ∈ I ∧ ℓ = f i then (1 : ℝ) else 0 := ⟨_, rfl⟩
  have hPnorm : ‖P‖ ≤ 1 := by
    rw [hP]
    exact l2_opNorm_rowSelect_le_one I f hf
  -- selecting the rows of `I` from the `m × n` iid matrix gives `X_N`
  have hsel : ∀ (y : Fin m × Fin n → EtaOutcome) (x' : Fin n × Fin n → EtaOutcome),
      ternMat B I (fun e => if e.1 ∈ I then y (f e.1, e.2) else x' e) = P * iidMat B y := by
    intro y x'
    ext i j
    rw [hP]
    simp only [ternMat, Matrix.of_apply, Matrix.mul_apply, iidMat]
    by_cases hi : i ∈ I
    · simp [hi]
    · simp [hi]
  -- the selection identity
  have hid := expect_select (TernaryJacobi.law B (Nat.zero_lt_of_lt hB))
    (fun e : Fin n × Fin n => e.1 ∈ I) (fun e => (f e.1, e.2))
    (fun e e' he he' hee => by
      obtain ⟨h1, h2⟩ := Prod.mk.inj hee
      exact Prod.ext (hf he he' h1) h2)
    (fun _ a => a) (fun _ _ => rfl) (fun _ _ => rfl) (fun z => ‖ternMat B I z * V‖)
  calc (ternLaw n B (Nat.zero_lt_of_lt hB)).expect (fun z => ‖ternMat B I z * V‖)
      = (FiniteLaw.independentProduct
          (fun _ : Fin m × Fin n => TernaryJacobi.law B (Nat.zero_lt_of_lt hB))).expect (fun y =>
          (FiniteLaw.independentProduct
            (fun _ : Fin n × Fin n => TernaryJacobi.law B (Nat.zero_lt_of_lt hB))).expect
            (fun x' => ‖ternMat B I (fun e => if e.1 ∈ I then y (f e.1, e.2) else x' e) * V‖)) :=
        hid.symm
    _ = (FiniteLaw.independentProduct
          (fun _ : Fin m × Fin n => TernaryJacobi.law B (Nat.zero_lt_of_lt hB))).expect
          (fun y => ‖P * iidMat B y * V‖) := by
        apply FiniteLaw.expect_congr
        intro y
        simp only [hsel, FiniteLaw.expect_const]
    _ ≤ (FiniteLaw.independentProduct
          (fun _ : Fin m × Fin n => TernaryJacobi.law B (Nat.zero_lt_of_lt hB))).expect
          (fun y => ‖iidMat B y * V‖) := by
        apply FiniteLaw.expect_mono
        intro y
        rw [Matrix.mul_assoc]
        calc ‖P * (iidMat B y * V)‖ ≤ ‖P‖ * ‖iidMat B y * V‖ := Matrix.l2_opNorm_mul _ _
          _ ≤ 1 * ‖iidMat B y * V‖ := mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)
          _ = ‖iidMat B y * V‖ := one_mul _
    _ = (ProductFock.iidLaw B hB m n).expect (fun x => ‖iidMat B x * V‖) := rfl

end Cross
end SparseStack
