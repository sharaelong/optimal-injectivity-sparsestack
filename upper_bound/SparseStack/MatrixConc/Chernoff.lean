import Mathlib
import SparseFockFormal.FiniteProbability
import SparseStack.MatrixConc.GoldenThompson
import SparseStack.MatrixConc.SpectralExp
import SparseStack.MatrixConc.Resample

/-!
# Isotropic matrix Chernoff bound (Ahlswede–Winter)

Let `X_ℓ = P ℓ (x ℓ)` be independent real PSD contractions (`0 ⪯ X_ℓ ⪯ 1`) with scalar means
`E X_ℓ = c_ℓ 1`, and `S = ∑ X_ℓ`. Then `E ‖S‖ ≤ (e - 1) ∑ c_ℓ + log d`.

Proof (Ahlswede–Winter, with `θ = 1`):
1. Golden–Thompson (`SparseStack.golden_thompson`): `tr exp (R + X) ≤ tr (exp R exp X)`.
2. One step (`aw_step`): for PSD `M`, `E tr (M exp X) ≤ E tr (M (1 + (e-1) X))
   = (1 + (e-1) c) tr M ≤ exp ((e-1) c) tr M`, using `exp X ⪯ 1 + (e-1) X` for `0 ⪯ X ⪯ 1`.
3. Iteration over the finite index set (`aw_iteration`), resampling one coordinate at a time
   (`SparseStack.MatrixConc.expect_resample`): `E tr exp S ≤ d exp ((e-1) ∑ c)`.
4. `exp ‖S‖ ≤ tr exp S` (`S ⪰ 0`, `d > 0`) and Jensen for `exp`:
   `exp (E ‖S‖) ≤ E exp ‖S‖ ≤ d exp ((e-1) ∑ c)`.
-/

open scoped Matrix.Norms.L2Operator

namespace SparseStack

open MatrixConc NormedSpace SparseFock

/-- One Ahlswede–Winter step: for PSD `M` and a random PSD contraction `P ω` with mean `c • 1`,
`∑ ω, ν ω * tr (M exp (P ω)) ≤ exp ((e - 1) c) * tr M`. -/
theorem aw_step {Ω : Type} [Fintype Ω] {d : ℕ} (ν : FiniteLaw Ω)
    (P : Ω → Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (hPsd : ∀ ω, (P ω).PosSemidef) (hPle : ∀ ω, (1 - P ω).PosSemidef)
    (hmean : ∑ ω, ν.weight ω • P ω = c • (1 : Matrix (Fin d) (Fin d) ℝ))
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosSemidef) :
    ∑ ω, ν.weight ω * (M * exp (P ω)).trace ≤ Real.exp ((Real.exp 1 - 1) * c) * M.trace := by
  have h1 : ∀ ω, ν.weight ω * (M * exp (P ω)).trace ≤
      ν.weight ω * (M.trace + (Real.exp 1 - 1) * (M * P ω).trace) := fun ω =>
    mul_le_mul_of_nonneg_left (trace_mul_exp_le M (P ω) hM (hPsd ω) (hPle ω))
      (ν.weight_nonneg ω)
  have hlin : ∑ ω, ν.weight ω * (M * P ω).trace = c * M.trace := by
    have h : (M * ∑ ω, ν.weight ω • P ω).trace =
        (M * (c • (1 : Matrix (Fin d) (Fin d) ℝ))).trace := by
      rw [hmean]
    rw [Matrix.mul_sum, Matrix.trace_sum] at h
    simpa only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_one] using h
  calc ∑ ω, ν.weight ω * (M * exp (P ω)).trace
      ≤ ∑ ω, ν.weight ω * (M.trace + (Real.exp 1 - 1) * (M * P ω).trace) :=
        Finset.sum_le_sum fun ω _ => h1 ω
    _ = (∑ ω, ν.weight ω) * M.trace +
          (Real.exp 1 - 1) * ∑ ω, ν.weight ω * (M * P ω).trace := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        ring
    _ = (1 + (Real.exp 1 - 1) * c) * M.trace := by
        rw [ν.sum_weight, hlin]
        ring
    _ ≤ Real.exp ((Real.exp 1 - 1) * c) * M.trace := by
        apply mul_le_mul_of_nonneg_right _ hM.trace_nonneg
        have := Real.add_one_le_exp ((Real.exp 1 - 1) * c)
        linarith

/-- Ahlswede–Winter iteration: `E tr exp (∑_{ℓ ∈ s} X_ℓ) ≤ d exp ((e - 1) ∑_{ℓ ∈ s} c_ℓ)`. -/
theorem aw_iteration {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω] {d : ℕ}
    (μ : ι → FiniteLaw Ω) (P : ι → Ω → Matrix (Fin d) (Fin d) ℝ) (c : ι → ℝ)
    (hPsd : ∀ ℓ ω, (P ℓ ω).PosSemidef) (hPle : ∀ ℓ ω, (1 - P ℓ ω).PosSemidef)
    (hmean : ∀ ℓ, ∑ ω, (μ ℓ).weight ω • P ℓ ω = c ℓ • (1 : Matrix (Fin d) (Fin d) ℝ))
    (s : Finset ι) :
    (FiniteLaw.independentProduct μ).expect (fun x => (exp (∑ ℓ ∈ s, P ℓ (x ℓ))).trace) ≤
      d * Real.exp ((Real.exp 1 - 1) * ∑ ℓ ∈ s, c ℓ) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [Matrix.trace_one]
  | insert a s ha ih =>
    have hpt : ∀ x : ι → Ω,
        ∑ ω, (μ a).weight ω *
            (exp (∑ ℓ ∈ insert a s, P ℓ (Function.update x a ω ℓ))).trace ≤
          Real.exp ((Real.exp 1 - 1) * c a) * (exp (∑ ℓ ∈ s, P ℓ (x ℓ))).trace := by
      intro x
      have hupd : ∀ ω, ∑ ℓ ∈ insert a s, P ℓ (Function.update x a ω ℓ) =
          (∑ ℓ ∈ s, P ℓ (x ℓ)) + P a ω := by
        intro ω
        rw [Finset.sum_insert ha, Function.update_self, add_comm (P a ω)]
        congr 1
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        rw [Function.update_of_ne (by rintro rfl; exact ha hℓ)]
      have hR : (∑ ℓ ∈ s, P ℓ (x ℓ)).IsHermitian :=
        (Matrix.posSemidef_sum s (fun ℓ _ => hPsd ℓ (x ℓ))).isHermitian
      have hM : (exp (∑ ℓ ∈ s, P ℓ (x ℓ))).PosSemidef := posSemidef_exp _ hR
      calc ∑ ω, (μ a).weight ω *
            (exp (∑ ℓ ∈ insert a s, P ℓ (Function.update x a ω ℓ))).trace
          ≤ ∑ ω, (μ a).weight ω * (exp (∑ ℓ ∈ s, P ℓ (x ℓ)) * exp (P a ω)).trace := by
            apply Finset.sum_le_sum
            intro ω _
            rw [hupd ω]
            exact mul_le_mul_of_nonneg_left
              (golden_thompson _ _ hR (hPsd a ω).isHermitian) ((μ a).weight_nonneg ω)
        _ ≤ Real.exp ((Real.exp 1 - 1) * c a) * (exp (∑ ℓ ∈ s, P ℓ (x ℓ))).trace :=
            aw_step (μ a) (P a) (c a) (hPsd a) (hPle a) (hmean a) _ hM
    calc (FiniteLaw.independentProduct μ).expect
          (fun x => (exp (∑ ℓ ∈ insert a s, P ℓ (x ℓ))).trace)
        = (FiniteLaw.independentProduct μ).expect (fun x => ∑ ω, (μ a).weight ω *
            (exp (∑ ℓ ∈ insert a s, P ℓ (Function.update x a ω ℓ))).trace) :=
          expect_resample μ a _
      _ ≤ (FiniteLaw.independentProduct μ).expect (fun x =>
            Real.exp ((Real.exp 1 - 1) * c a) * (exp (∑ ℓ ∈ s, P ℓ (x ℓ))).trace) :=
          FiniteLaw.expect_mono _ hpt
      _ = Real.exp ((Real.exp 1 - 1) * c a) * (FiniteLaw.independentProduct μ).expect
            (fun x => (exp (∑ ℓ ∈ s, P ℓ (x ℓ))).trace) :=
          FiniteLaw.expect_smul _ _ _
      _ ≤ Real.exp ((Real.exp 1 - 1) * c a) *
            (d * Real.exp ((Real.exp 1 - 1) * ∑ ℓ ∈ s, c ℓ)) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = d * Real.exp ((Real.exp 1 - 1) * ∑ ℓ ∈ insert a s, c ℓ) := by
          rw [Finset.sum_insert ha, mul_add, Real.exp_add]
          ring

/-- Jensen's inequality for `exp` under a finite law: `exp (E f) ≤ E exp f`. -/
theorem exp_expect_le_expect_exp {α : Type} [Fintype α] (ν : FiniteLaw α) (f : α → ℝ) :
    Real.exp (ν.expect f) ≤ ν.expect (fun x => Real.exp (f x)) := by
  have hpt : ∀ x, Real.exp (ν.expect f) * (1 + (f x - ν.expect f)) ≤ Real.exp (f x) := by
    intro x
    have h := Real.add_one_le_exp (f x - ν.expect f)
    calc Real.exp (ν.expect f) * (1 + (f x - ν.expect f))
        ≤ Real.exp (ν.expect f) * Real.exp (f x - ν.expect f) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          linarith
      _ = Real.exp (f x) := by
          rw [← Real.exp_add]
          ring_nf
  have hE : ν.expect (fun x => Real.exp (ν.expect f) * (1 + (f x - ν.expect f))) =
      Real.exp (ν.expect f) := by
    rw [FiniteLaw.expect_smul, FiniteLaw.expect_add ν (fun _ => 1) (fun x => f x - ν.expect f),
      FiniteLaw.expect_sub ν f (fun _ => ν.expect f), FiniteLaw.expect_one,
      FiniteLaw.expect_const]
    ring
  calc Real.exp (ν.expect f)
      = ν.expect (fun x => Real.exp (ν.expect f) * (1 + (f x - ν.expect f))) := hE.symm
    _ ≤ ν.expect (fun x => Real.exp (f x)) := FiniteLaw.expect_mono _ hpt

/-- Isotropic matrix Chernoff bound (Ahlswede–Winter via Golden–Thompson): independent PSD contractions with
scalar means. Replaces the paper's use of matrix Bernstein (Tropp Thm 6.1.1) for the diagonal part `D` in
Lemma `lem:iid-norm`. -/
theorem isotropic_matrix_chernoff {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω] {d : ℕ}
    (hd : 0 < d) (μ : ι → SparseFock.FiniteLaw Ω) (P : ι → Ω → Matrix (Fin d) (Fin d) ℝ) (c : ι → ℝ)
    (hPsd : ∀ ℓ ω, (P ℓ ω).PosSemidef) (hPle : ∀ ℓ ω, (1 - P ℓ ω).PosSemidef)
    (hmean : ∀ ℓ, ∑ ω, (μ ℓ).weight ω • P ℓ ω = c ℓ • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    (SparseFock.FiniteLaw.independentProduct μ).expect (fun x => ‖∑ ℓ, P ℓ (x ℓ)‖) ≤
      (Real.exp 1 - 1) * ∑ ℓ, c ℓ + Real.log d := by
  have hne : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hS : ∀ x : ι → Ω, (∑ ℓ, P ℓ (x ℓ)).PosSemidef := fun x =>
    Matrix.posSemidef_sum _ (fun ℓ _ => hPsd ℓ (x ℓ))
  have hexpf : ∀ x : ι → Ω,
      Real.exp ‖∑ ℓ, P ℓ (x ℓ)‖ ≤ (exp (∑ ℓ, P ℓ (x ℓ))).trace := fun x =>
    exp_norm_le_trace_exp _ (hS x)
  have hAW := aw_iteration μ P c hPsd hPle hmean Finset.univ
  have h1 : Real.exp ((SparseFock.FiniteLaw.independentProduct μ).expect
      (fun x => ‖∑ ℓ, P ℓ (x ℓ)‖)) ≤ d * Real.exp ((Real.exp 1 - 1) * ∑ ℓ, c ℓ) :=
    calc Real.exp ((SparseFock.FiniteLaw.independentProduct μ).expect
          (fun x => ‖∑ ℓ, P ℓ (x ℓ)‖))
        ≤ (SparseFock.FiniteLaw.independentProduct μ).expect
            (fun x => Real.exp ‖∑ ℓ, P ℓ (x ℓ)‖) :=
          exp_expect_le_expect_exp _ _
      _ ≤ (SparseFock.FiniteLaw.independentProduct μ).expect
            (fun x => (exp (∑ ℓ, P ℓ (x ℓ))).trace) :=
          FiniteLaw.expect_mono _ hexpf
      _ ≤ d * Real.exp ((Real.exp 1 - 1) * ∑ ℓ, c ℓ) := hAW
  have h2 : Real.exp ((SparseFock.FiniteLaw.independentProduct μ).expect
      (fun x => ‖∑ ℓ, P ℓ (x ℓ)‖)) ≤
      Real.exp ((Real.exp 1 - 1) * ∑ ℓ, c ℓ + Real.log d) := by
    rw [Real.exp_add, Real.exp_log hd', mul_comm (Real.exp _)]
    exact h1
  exact Real.exp_le_exp.mp h2

end SparseStack
