import Mathlib

/-!
# Lieb–Thirring trace inequality for powers of two

For real symmetric matrices `A B` and `k = 2 ^ j` we prove
`tr ((A * B) ^ k) ≤ tr (A ^ k * B ^ k)`.

The proof is the classical elementary joint induction on `j` of the two statements

* `S(l)`: for every real square `X`, `|tr (X ^ (2 l))| ≤ tr ((Xᵀ * X) ^ l)`;
* `LT(l)`: for symmetric `A B`, `tr ((A * B) ^ l) ≤ tr (A ^ l * B ^ l)`;

for `l = 2 ^ j`.

* Base `l = 1`: `S(1)` is the Frobenius Cauchy–Schwarz inequality `|tr (X X)| ≤ tr (Xᵀ X)`
  (obtained from `tr ((X ∓ Xᵀ)ᵀ (X ∓ Xᵀ)) ≥ 0`), and `LT(1)` is trivial.
* `S(l) ∧ LT(l) → S(2l)`: `|tr (X^(4l))| = |tr ((X²)^(2l))| ≤ tr (((X²)ᵀ X²)^l)
  = tr ((Y Y')^l)` with `Y = XᵀX`, `Y' = XXᵀ` (cyclicity), then `LT(l)` and the
  arithmetic–geometric form of Cauchy–Schwarz `2 tr (M N) ≤ tr (M M) + tr (N N)` for symmetric
  `M = Y^l`, `N = Y'^l`, together with `tr (Y'^(2l)) = tr (Y^(2l))`.
* `S(l) ∧ LT(l) → LT(2l)`: `tr ((AB)^(2l)) ≤ tr (((AB)ᵀ (AB))^l) = tr ((A² B²)^l)
  ≤ tr (A^(2l) B^(2l))` (`LT(l)` applied to the symmetric pair `A², B²`).

Only symmetry (not positivity) is needed. No real exponents or square roots appear.
-/

namespace SparseStack

namespace MatrixConc

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Cyclicity of the trace for powers of a product: `tr ((M N)^l) = tr ((N M)^l)`. -/
theorem trace_mul_pow_comm (M N : Matrix n n ℝ) (l : ℕ) :
    ((M * N) ^ l).trace = ((N * M) ^ l).trace := by
  cases l with
  | zero => simp
  | succ k =>
    calc ((M * N) ^ (k + 1)).trace = (M * ((N * M) ^ k * N)).trace := by
          rw [pow_succ, ← mul_assoc, mul_pow_mul, mul_assoc]
      _ = ((N * M) ^ k * N * M).trace := Matrix.trace_mul_comm _ _
      _ = ((N * M) ^ (k + 1)).trace := by rw [mul_assoc, ← pow_succ]

omit [DecidableEq n] in
/-- The Frobenius square `tr (Yᵀ Y) = ∑ Y_ij²` is nonnegative. -/
theorem trace_transpose_mul_self_nonneg (Y : Matrix n n ℝ) : 0 ≤ (Yᵀ * Y).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => mul_self_nonneg _

omit [DecidableEq n] in
/-- Frobenius Cauchy–Schwarz: `|tr (X X)| ≤ tr (Xᵀ X)`. -/
theorem abs_trace_mul_self_le (X : Matrix n n ℝ) : |(X * X).trace| ≤ (Xᵀ * X).trace := by
  have h1 := trace_transpose_mul_self_nonneg (X - Xᵀ)
  have h2 := trace_transpose_mul_self_nonneg (X + Xᵀ)
  have e1 : (Xᵀ * Xᵀ).trace = (X * X).trace := by
    rw [← Matrix.transpose_mul, Matrix.trace_transpose]
  have e2 : (X * Xᵀ).trace = (Xᵀ * X).trace := Matrix.trace_mul_comm _ _
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.trace_sub,
    Matrix.trace_add] at h1 h2
  rw [abs_le]
  constructor <;> linarith

omit [DecidableEq n] in
/-- Arithmetic–geometric form of the Frobenius Cauchy–Schwarz inequality for symmetric matrices:
`2 tr (M N) ≤ tr (M M) + tr (N N)`. -/
theorem two_mul_trace_mul_le (M N : Matrix n n ℝ) (hM : Mᵀ = M) (hN : Nᵀ = N) :
    2 * (M * N).trace ≤ (M * M).trace + (N * N).trace := by
  have h := trace_transpose_mul_self_nonneg (M - N)
  have e : (N * M).trace = (M * N).trace := Matrix.trace_mul_comm _ _
  rw [Matrix.transpose_sub, hM, hN] at h
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub] at h
  linarith

/-- The joint induction `S(2^j) ∧ LT(2^j)`. -/
theorem lieb_thirring_aux (j : ℕ) :
    (∀ X : Matrix n n ℝ, |(X ^ (2 * 2 ^ j)).trace| ≤ ((Xᵀ * X) ^ (2 ^ j)).trace) ∧
    (∀ A B : Matrix n n ℝ, Aᵀ = A → Bᵀ = B →
      ((A * B) ^ (2 ^ j)).trace ≤ (A ^ (2 ^ j) * B ^ (2 ^ j)).trace) := by
  induction j with
  | zero =>
    refine ⟨fun X => ?_, fun A B _ _ => ?_⟩
    · simpa [sq] using abs_trace_mul_self_le X
    · simp
  | succ j ih =>
    obtain ⟨hS, hLT⟩ := ih
    have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
    refine ⟨fun X => ?_, fun A B hA hB => ?_⟩
    · -- `S(2l)`
      have hY : (Xᵀ * X)ᵀ = Xᵀ * X := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      have hY' : (X * Xᵀ)ᵀ = X * Xᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      have step1 : |(X ^ (2 * 2 ^ (j + 1))).trace| ≤
          (((X ^ 2)ᵀ * X ^ 2) ^ (2 ^ j)).trace := by
        have h := hS (X ^ 2)
        rwa [← pow_mul, ← mul_assoc, mul_comm 2 2, mul_assoc, ← hpow] at h
      have step2 : (((X ^ 2)ᵀ * X ^ 2) ^ (2 ^ j)).trace =
          (((Xᵀ * X) * (X * Xᵀ)) ^ (2 ^ j)).trace := by
        rw [Matrix.transpose_pow, sq, sq]
        calc ((Xᵀ * Xᵀ * (X * X)) ^ 2 ^ j).trace = ((Xᵀ * (Xᵀ * (X * X))) ^ 2 ^ j).trace := by
              rw [mul_assoc]
          _ = (((Xᵀ * (X * X)) * Xᵀ) ^ 2 ^ j).trace := trace_mul_pow_comm _ _ _
          _ = (((Xᵀ * X) * (X * Xᵀ)) ^ (2 ^ j)).trace := by simp only [mul_assoc]
      have step3 := hLT _ _ hY hY'
      have step4 := two_mul_trace_mul_le ((Xᵀ * X) ^ 2 ^ j) ((X * Xᵀ) ^ 2 ^ j)
        (by rw [Matrix.transpose_pow, hY]) (by rw [Matrix.transpose_pow, hY'])
      have e1 : ((Xᵀ * X) ^ 2 ^ j * (Xᵀ * X) ^ 2 ^ j).trace =
          ((Xᵀ * X) ^ 2 ^ (j + 1)).trace := by
        rw [← pow_add, hpow, two_mul]
      have e2 : ((X * Xᵀ) ^ 2 ^ j * (X * Xᵀ) ^ 2 ^ j).trace =
          ((Xᵀ * X) ^ 2 ^ (j + 1)).trace := by
        rw [← pow_add, trace_mul_pow_comm, hpow, two_mul]
      linarith
    · -- `LT(2l)`
      have hAA : (A * A)ᵀ = A * A := by rw [Matrix.transpose_mul, hA]
      have hBB : (B * B)ᵀ = B * B := by rw [Matrix.transpose_mul, hB]
      have step1 := hS (A * B)
      have step2 : (((A * B)ᵀ * (A * B)) ^ 2 ^ j).trace =
          (((A * A) * (B * B)) ^ 2 ^ j).trace := by
        rw [Matrix.transpose_mul, hA, hB]
        calc ((B * A * (A * B)) ^ 2 ^ j).trace = ((B * (A * A * B)) ^ 2 ^ j).trace := by
              simp only [mul_assoc]
          _ = ((A * A * B * B) ^ 2 ^ j).trace := trace_mul_pow_comm _ _ _
          _ = (((A * A) * (B * B)) ^ 2 ^ j).trace := by simp only [mul_assoc]
      have step3 := hLT _ _ hAA hBB
      have e : (A * A) ^ 2 ^ j * (B * B) ^ 2 ^ j = A ^ 2 ^ (j + 1) * B ^ 2 ^ (j + 1) := by
        rw [hpow, pow_mul, pow_mul, sq, sq]
      rw [← e, hpow]
      have := le_abs_self ((A * B) ^ (2 * 2 ^ j)).trace
      linarith

/-- **Lieb–Thirring inequality for powers of two.** For real symmetric matrices `A B` and
`k = 2 ^ j`, `tr ((A * B) ^ k) ≤ tr (A ^ k * B ^ k)`. -/
theorem lieb_thirring_pow_two (A B : Matrix n n ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (j : ℕ) : ((A * B) ^ (2 ^ j)).trace ≤ (A ^ (2 ^ j) * B ^ (2 ^ j)).trace :=
  (lieb_thirring_aux j).2 A B (Matrix.isHermitian_iff_isSymm.mp hA)
    (Matrix.isHermitian_iff_isSymm.mp hB)

end MatrixConc

end SparseStack
