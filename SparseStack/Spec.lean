import Mathlib

/-!
# Spec: constant injection for a sparse stacked sketch (`thm:main`)

This file states the core theorem `thm:main` ("Constant injection for a sparse stacked
sketch"). It imports only Mathlib and contains only plain definitions; the headline statements are
the `Prop`-valued definitions at the end. Nothing in this file is proved.

## Model

* **Randomness.** For `s` blocks, `b` buckets and `n` input coordinates, a sample point is a pair
  `(h, σ)` with `h : Fin s → Fin n → Fin b` (the hash `h_t(i)`) and `σ : Fin s → Fin n → Bool`
  (the sign bit of `σ_{ti}`: `true ↦ +1`, `false ↦ -1`). The sample space is the finite product
  type, and probabilities and expectations are taken under the **uniform** distribution on it.
  The uniform distribution on this product is exactly the joint law of independent hashes, each
  uniform on `[b]`, and independent signs, each uniform on `{-1, 1}`.
* **Sketch.** `Π_{s,b} = s^{-1/2} col(S_1, …, S_s)`, where `S_t ∈ ℝ^{b×n}` has columns
  `S_t e_i = σ_{ti} e_{h_t(i)}`. Rows of `Π` are indexed by pairs `(t, u) ∈ Fin s × Fin b`
  (block `t`, bucket `u`), so `Π[(t,u), i] = s^{-1/2} σ_{ti} [h_t(i) = u]`. `Ω = Πᵀ`.
* **Smallest eigenvalue.** `λ_min(AᵀA) ≥ α` is stated as "every eigenvalue of the symmetric
  matrix `AᵀA` is at least `α`" (`MinEigenvalueAtLeast`). For a real matrix the conjugate transpose
  `Aᴴ` is the transpose `Aᵀ`. An equivalent quadratic-form version (`‖Ax‖² ≥ α‖x‖²` for all `x`) is
  stated as a second headline.
-/

namespace SparseStack

/-! ## Finite uniform probability -/

/-- The probability of the event `E` under the uniform distribution on the finite type `Ω`:
`#{ω | E ω} / #Ω`. -/
noncomputable def uniformProb (Ω : Type) [Fintype Ω] (E : Ω → Prop) : ℝ :=
  (Nat.card {ω : Ω // E ω} : ℝ) / (Fintype.card Ω : ℝ)

/-- The expectation of a matrix-valued function under the uniform distribution on the finite type
`Ω`: `(1/#Ω) ∑_ω f ω`. -/
noncomputable def uniformMeanMatrix {Ω : Type} [Fintype Ω] {m k : Type}
    (f : Ω → Matrix m k ℝ) : Matrix m k ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ • ∑ ω, f ω

/-! ## The SparseStack sketch -/

/-- The sign `±1` encoded by a bit: `true ↦ 1`, `false ↦ -1`. -/
def signValue (β : Bool) : ℝ := if β then 1 else -1

/-- The SparseStack sample space with `s` blocks, `b` buckets and `n` input coordinates:
hashes `h t i ∈ Fin b` and sign bits `σ t i`, for every block `t` and input coordinate `i`. -/
abbrev SketchSample (s b n : ℕ) : Type :=
  (Fin s → Fin n → Fin b) × (Fin s → Fin n → Bool)

/-- The SparseStack matrix `Π_{s,b} ∈ ℝ^{(s·b) × n}` of a sample point `(h, σ)`:
`Π[(t,u), i] = s^{-1/2} · σ_{ti} · [h_t(i) = u]`. -/
noncomputable def sketchMatrix {s b n : ℕ} (ω : SketchSample s b n) :
    Matrix (Fin s × Fin b) (Fin n) ℝ :=
  fun p i => (Real.sqrt (s : ℝ))⁻¹ * (if ω.1 p.1 i = p.2 then signValue (ω.2 p.1 i) else 0)

/-- The sketch `Ω = Π_{s,b}ᵀ ∈ ℝ^{n × (s·b)}`. -/
noncomputable def sketchOmega {s b n : ℕ} (ω : SketchSample s b n) :
    Matrix (Fin n) (Fin s × Fin b) ℝ :=
  (sketchMatrix ω).transpose

/-! ## Constants and parameters of `thm:main` -/

/-- `C = 32768`. -/
def constC : ℕ := 32768

/-- `K = 160000000`. -/
def constK : ℕ := 160000000

/-- `α = 12256937 / 119880000000`. -/
noncomputable def constAlpha : ℝ := 12256937 / 119880000000

/-- The number of blocks `ζ = ⌈C √(log(e r))⌉` (natural logarithm). -/
noncomputable def numBlocks (r : ℕ) : ℕ :=
  Nat.ceil ((constC : ℝ) * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))))

/-- The number of buckets `b = ⌈K r / ζ⌉`. -/
noncomputable def numBuckets (r : ℕ) : ℕ :=
  Nat.ceil ((constK : ℝ) * (r : ℝ) / (numBlocks r : ℝ))

/-! ## The smallest-eigenvalue event -/

/-- `λ_min(AᵀA) ≥ α`: every eigenvalue of the symmetric matrix `AᵀA` (written `Aᴴ * A`, which is
`Aᵀ * A` for real matrices) is at least `α`. -/
def MinEigenvalueAtLeast {k r : Type} [Fintype k] [Fintype r] [DecidableEq r]
    (A : Matrix k r ℝ) (α : ℝ) : Prop :=
  ∀ j : r, α ≤ (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j

/-- Quadratic-form version of `λ_min(AᵀA) ≥ α`: `α ‖x‖² ≤ ‖A x‖²` for every `x`. -/
def QuadraticLowerBound {k r : Type} [Fintype k] [Fintype r]
    (A : Matrix k r ℝ) (α : ℝ) : Prop :=
  ∀ x : r → ℝ, α * dotProduct x x ≤ dotProduct (Matrix.mulVec A x) (Matrix.mulVec A x)

/-! ## Headline statements -/

/-- `thm:main`, probability clause: for every `n ≥ r ≥ 2` and every fixed `Q ∈ ℝ^{n×r}` with
`QᵀQ = I_r`, with `ζ = numBlocks r` and `b = numBuckets r`, the matrix `A = Π_{ζ,b} Q` satisfies
`Pr{λ_min(AᵀA) ≥ α} ≥ 19/20`. -/
def ConstantInjection : Prop :=
  ∀ n r : ℕ, 2 ≤ r → r ≤ n →
    ∀ Q : Matrix (Fin n) (Fin r) ℝ, Q.transpose * Q = 1 →
      (19 / 20 : ℝ) ≤ uniformProb (SketchSample (numBlocks r) (numBuckets r) n)
        (fun ω => MinEigenvalueAtLeast (sketchMatrix ω * Q) constAlpha)

/-- The same clause with `λ_min(AᵀA) ≥ α` written as `α ‖x‖² ≤ ‖A x‖²` for all `x ∈ ℝ^r`. -/
def ConstantInjectionQuadratic : Prop :=
  ∀ n r : ℕ, 2 ≤ r → r ≤ n →
    ∀ Q : Matrix (Fin n) (Fin r) ℝ, Q.transpose * Q = 1 →
      (19 / 20 : ℝ) ≤ uniformProb (SketchSample (numBlocks r) (numBuckets r) n)
        (fun ω => QuadraticLowerBound (sketchMatrix ω * Q) constAlpha)

/-- `thm:main`, "Moreover" clause 1: `E Ω Ωᵀ = I_n` for the parameters `ζ = numBlocks r`,
`b = numBuckets r` of the theorem, for every `n ≥ r ≥ 2`. -/
def MeanIdentity : Prop :=
  ∀ n r : ℕ, 2 ≤ r → r ≤ n →
    uniformMeanMatrix
        (fun ω : SketchSample (numBlocks r) (numBuckets r) n =>
          sketchOmega ω * (sketchOmega ω).transpose) = 1

/-- `thm:main`, "Moreover" clause 2: `b ζ ≤ K r + ζ ≤ (K + C + 1) r` for every `r ≥ 2`. -/
def SizeBounds : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    numBuckets r * numBlocks r ≤ constK * r + numBlocks r ∧
      constK * r + numBlocks r ≤ (constK + constC + 1) * r

/-- `thm:main`, "In particular": `α > 10^{-4}`. -/
def AlphaBound : Prop :=
  (1 : ℝ) / 10000 < constAlpha

/-- `thm:main` in full: the probability clause, both "Moreover" clauses and `α > 10^{-4}`. -/
def MainTheorem : Prop :=
  ConstantInjection ∧ MeanIdentity ∧ SizeBounds ∧ AlphaBound

end SparseStack
