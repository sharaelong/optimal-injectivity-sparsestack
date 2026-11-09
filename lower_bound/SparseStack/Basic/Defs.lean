import Mathlib
import SparseStack.Spec

/-!
# Basic definitions shared by the blueprint (lead-owned)

Conventions used throughout the blueprint:
* vectors are functions `Fin k → ℝ` (or `ι → ℝ`); squared Euclidean norms are written with
  `sqNorm v = dotProduct v v` (never the sup norm `‖v‖` of `Pi` types);
* matrix operator norms `‖A‖` are the L2 operator norms of `Matrix.Norms.L2Operator`
  (the convention of Heidary's `SparseFock.MatrixTail`);
* the paper's `d_m(z) = min_{|I| ≤ m} ‖z_{Iᶜ}‖` is used in squared form `distSparseSq m z`.
-/

namespace SparseStack

open Matrix

/-- Squared Euclidean norm `‖v‖² = ∑ v_i²` of a real vector. -/
def sqNorm {ι : Type} [Fintype ι] (v : ι → ℝ) : ℝ := dotProduct v v

/-- Squared Frobenius norm `‖A‖_F² = ∑_{i,j} A_ij²`. -/
def frobSq {k l : Type} [Fintype k] [Fintype l] (A : Matrix k l ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- Squared `d_m`: `d_m(z)² = min_{|I| ≤ m} ∑_{i ∉ I} z_i²` (paper, line 303). -/
noncomputable def distSparseSq (m : ℕ) {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  ⨅ I : {I : Finset (Fin n) // I.card ≤ m}, ∑ i ∈ (I.1)ᶜ, z i ^ 2

/-- Coordinate restriction `E_I v` (keep coordinates in `I`, zero elsewhere). -/
def restrictVec {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ I then v i else 0

/-! ## Constants of the Method-D completion with `ε = 1/3`, `t₀ = 11/48`, `κ = 1` -/

/-- `ρ₀ = 499/1000`. -/
noncomputable def rho0 : ℝ := 499 / 1000

/-- `t₀ = 11/48`. -/
noncomputable def t0 : ℝ := 11 / 48

/-- `a₀ = 11/12`. -/
noncomputable def a0 : ℝ := 11 / 12

/-- `β = ρ₀ (a₀ - 2 t₀) = 5489/24000`. -/
noncomputable def betaRep : ℝ := 5489 / 24000

/-- `γ = β + t₀ = 3663/8000`. -/
noncomputable def gammaRep : ℝ := 3663 / 8000

/-- `λ² = 121/45000` (with `λ = (99/100) √(2/81) ε`, `ε = 1/3`). -/
noncomputable def lambdaSq : ℝ := 121 / 45000

/-- `u = (8/3) ε² = 8/27`. -/
noncomputable def uCert : ℝ := 8 / 27

/-- `v = 8/(3 λ²) = 120000/121`. -/
noncomputable def vCert : ℝ := 120000 / 121

/-- `C⋆ = ρ₀ χ C = 255232512/15625`. -/
noncomputable def cStarRep : ℝ := 255232512 / 15625

/-- `K⋆ = ρ₀ K / κ = 79840000`. -/
def kStarRep : ℕ := 79840000

/-- `M = 440000` (localization width). -/
def locM : ℕ := 440000

/-- `Θ = 48800`. -/
def locTheta : ℕ := 48800

/-- The localization width `m = ⌈M r / s⌉`. -/
noncomputable def locWidth (r s : ℕ) : ℕ := Nat.ceil ((locM : ℝ) * (r : ℝ) / (s : ℝ))

/-! ## The retained-row cross-Gram matrix (paper, Lemma `lem:cross`) -/

/-- Number of coordinates of `I` hashed to bucket `u` in block `t`. -/
noncomputable def bucketLoad {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n)
    (t : Fin s) (u : Fin b) : ℕ :=
  (I.filter (fun i => ω.1 t i = u)).card

/-- The diagonal 0/1 matrix `T` retaining exactly the output rows `(t,u)` that contain exactly one
coordinate of `I`. -/
noncomputable def retainMatrix {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n) :
    Matrix (Fin s × Fin b) (Fin s × Fin b) ℝ :=
  Matrix.diagonal (fun p => if bucketLoad I ω p.1 p.2 = 1 then 1 else 0)

/-- Diagonal projection onto the coordinates in `I`. -/
noncomputable def coordProj {n : ℕ} (I : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => if i ∈ I then 1 else 0)

/-- The cross-Gram matrix `H̃ᵀ Ỹ` of the paper, written on `ℝⁿ`: rows indexed by all coordinates
(zero outside `I`), with `H̃ = T Π E_I` and `Ỹ = T Π V`. -/
noncomputable def crossGram {s b n d : ℕ} (I : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ)
    (ω : SketchSample s b n) : Matrix (Fin n) (Fin d) ℝ :=
  (retainMatrix I ω * sketchMatrix ω * coordProj I).transpose *
    (retainMatrix I ω * sketchMatrix ω * V)

/-- Head/background merge: coordinates in `I` (hashes and signs, all blocks) from `ω₀`, all other
coordinates from `ω`. Conditioning on the head is averaging over `ω` with `ω₀` fixed. -/
def mergeHead {s b n : ℕ} (I : Finset (Fin n)) (ω₀ ω : SketchSample s b n) :
    SketchSample s b n :=
  (fun t i => if i ∈ I then ω₀.1 t i else ω.1 t i,
   fun t i => if i ∈ I then ω₀.2 t i else ω.2 t i)

end SparseStack
