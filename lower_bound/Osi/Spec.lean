import Mathlib

/-!
# Specification: *Optimal Injectivity of the SparseStack* (Sections 1–10)

This file is the formal specification (`Osi/Spec.lean`) for the complete 50-page paper
*"Optimal Injectivity of the SparseStack"* (`source/constant_injectivity_sparsestack.pdf`,
SHA-256 `045f0795c68732002391ebbe773dfa4bcf7e43866484f00a5af1f8ed5a1e9588`).

It imports only `Mathlib` and contains plain, textbook mathematical definitions together with
`Prop`-valued statements of all main theorems, propositions, and lemmas across Sections 1–10:

* **Section 1.1 (Main Results & Tightness):**
  * `Theorem_1_1_GeneralParams`, `Theorem_1_1_PaperRange`, `Theorem_1_1_Schedule` (Theorem 1.1)
  * `SatisfiesOverlapCond` (Definition 1.2) and `Proposition_SparseStack_Overlap`
  * `Theorem_1_3_LowerBound`, `Theorem_1_3_LowerBound_HalfProb`, `Theorem_1_3_QuadraticN`
    (Theorem 1.3), and `Theorem_1_3_NecessityOfAmbientBound` (necessity of `n > K r`)
  * `Theorem_Optimal_SparseStack_Tightness` (unified shared-vocabulary tightness theorem)
* **Sections 2–6 (Upper-Bound Pipeline):**
  * `Theorem_2_1_FlatPreservation` (Theorem 2.1), `Theorem_2_2_CommonSupport` (Theorem 2.2),
    `Theorem_2_3_HeavyPreservation` (Theorem 2.3)
  * `Lemma_3_2_WeightedBernoulli` (Lemma 3.2), `Lemma_3_3_PointwiseFlat` (Lemma 3.3),
    `Lemma_3_4_LatticeRounding` (Lemma 3.4)
  * `Lemma_4_1_GaussianTruncation` (Lemma 4.1), `Lemma_4_2_MinimaxSelection` (Lemma 4.2)
  * `Lemma_5_3_IidOpNorm` (Lemma 5.3), `Lemma_5_4_IsolatedCrossTerm` (Lemma 5.4),
    `Lemma_5_5_FullSketchMoment` (Lemma 5.5)
  * `Lemma_6_1_SingleGroup` (Lemma 6.1), `Lemma_6_2_TwoGroupIsolation` (Lemma 6.2),
    `Lemma_6_3_TwoGroupHeavy` (Lemma 6.3)
* **Sections 8–10 (Lower-Bound Pipeline):**
  * `Lemma_8_1_HeavyRowCount` (Lemma 8.1), `Lemma_8_2_SmallOrOneSparseElim` (Lemma 8.2),
    `Lemma_8_3_C4FreeSubgraph` (Lemma 8.3)
  * `Lemma_9_1_TreeCancellation` (Lemma 9.1), `Lemma_9_2_SingleTreeDisjointLeaves` (Lemma 9.2),
    `Lemma_9_3_TuranCaroWei` (Lemma 9.3), `Lemma_9_4_TuranCenterRows` (Lemma 9.4),
    `Lemma_9_5_HallMarriage` (Lemma 9.5), `Lemma_9_6_DisjointLeafReservoirs` (Lemma 9.6),
    `Theorem_9_7_WitnessForest` (Theorem 9.7)
  * `Lemma_10_1_CoordinateSubspaceReduction` (Lemma 10.1),
    `Theorem_10_2_FiniteScale` (Theorem 10.2)
-/

namespace Osi
namespace Spec

/-! ## 1. Linear-algebraic primitives -/

/-- Squared Euclidean norm `‖v‖₂² = ∑ᵢ vᵢ²` of a finite-dimensional real vector. -/
def vecSqNorm {n : Type} [Fintype n] (v : n → ℝ) : ℝ :=
  ∑ i : n, (v i) ^ 2

/-- Squared Frobenius norm `‖A‖_F² = ∑ᵢ ∑ⱼ Aᵢⱼ²` of a real matrix. -/
def frobSq {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ :=
  ∑ i : m, ∑ j : n, (A i j) ^ 2

/-- Spectral (`ℓ₂ → ℓ₂` operator) norm `‖A‖ = ‖toContinuousLinearMap (toEuclideanLin A)‖` of a
real matrix (definitionally equal to `‖A‖` under `Matrix.Norms.L2Operator`). -/
noncomputable def spectralNorm {m l : Type} [Fintype m] [Fintype l] [DecidableEq l]
    (A : Matrix m l ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-- Loewner semidefinite order `A ⪯ B` on square real matrices: `B - A` is positive semidefinite. -/
def LoewnerLe {d : Type} [Fintype d] [DecidableEq d] (A B : Matrix d d ℝ) : Prop :=
  (B - A).PosSemidef

/-- `Q ∈ ℝ^{n×r}` is an isometry (orthonormal columns): `Qᵀ Q = I_r`. -/
def IsIsometry {n r : Type} [Fintype n] [Fintype r] [DecidableEq r]
    (Q : Matrix n r ℝ) : Prop :=
  Q.transpose * Q = 1

/-- Smallest-singular-value bound `σ_min(A)² = λ_min(Aᵀ A) ≥ α`, expressed via all eigenvalues of
the symmetric Gram matrix `Aᴴ A = Aᵀ A`. -/
def MinEigenvalueAtLeast {k r : Type} [Fintype k] [Fintype r] [DecidableEq r]
    (A : Matrix k r ℝ) (α : ℝ) : Prop :=
  ∀ j : r, α ≤ (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j

/-- Quadratic-form version of `σ_min(A)² ≥ α`: `α ‖x‖₂² ≤ ‖A x‖₂²` for all `x ∈ ℝ^r`. -/
def QuadraticLowerBound {k r : Type} [Fintype k] [Fintype r]
    (A : Matrix k r ℝ) (α : ℝ) : Prop :=
  ∀ x : r → ℝ, α * vecSqNorm x ≤ vecSqNorm (A.mulVec x)

/-- Squared `ℓ₂` distance `d_m(z)² = min_{|I| ≤ m} ∑_{i ∉ I} zᵢ²` from `z ∈ ℝ^n` to `m`-sparse
vectors (Section 2, p. 7; Section 3, p. 15). -/
noncomputable def distSparseSq {n : ℕ} (m : ℕ) (z : Fin n → ℝ) : ℝ :=
  ⨅ I : {I : Finset (Fin n) // I.card ≤ m}, ∑ i ∈ (I.1)ᶜ, (z i) ^ 2

/-- Coordinate restriction `v_I ∈ ℝ^n` retaining entries in `I` and zeroing out `Iᶜ`. -/
def coordVec {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ I then v i else 0

/-- Row-restricted matrix `Q_I ∈ ℝ^{n×r}` retaining rows in `I` and zeroing out rows outside `I`
(so `(Q_I)ᵀ (Q_I) = ∑_{i ∈ I} qᵢ qᵢᵀ`). -/
def coordRows {n r : ℕ} (I : Finset (Fin n)) (Q : Matrix (Fin n) (Fin r) ℝ) :
    Matrix (Fin n) (Fin r) ℝ :=
  fun i j => if i ∈ I then Q i j else 0

/-- Orthonormal coordinate-subspace frame `Q_R ∈ ℝ^{n×r}` associated with an `r`-element subset
`R ⊆ [n]` (`hR : R.card = r`), whose columns are the standard basis vectors `eᵢ` (`i ∈ R`) in
increasing index order; `(Sᵀ Q_R)` is the transposed row-submatrix `S_Rᵀ ∈ ℝ^{k×r}`. -/
noncomputable def coordFrame {n r : ℕ} (R : Finset (Fin n)) (hR : R.card = r) :
    Matrix (Fin n) (Fin r) ℝ :=
  fun i j => if i = R.orderEmbOfFin hR j then 1 else 0

/-! ## 2. Row sparsity, support overlap (Definition 1.2), and random sketching predicates -/

/-- Support `supp(sᵢ) = {j ∈ [k] : Sᵢⱼ ≠ 0}` of the `i`-th row of `S ∈ ℝ^{n×k}`. -/
noncomputable def rowSupport {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (i : Fin n) :
    Finset (Fin k) :=
  (Set.toFinite {j : Fin k | S i j ≠ 0}).toFinset

/-- Ordered pairs `(u, v)` (`u < v`) of distinct rows of `S` whose supports share at least two
column indices (`|supp(s_u) ∩ supp(s_v)| ≥ 2`). -/
noncomputable def overlapPairs {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) :
    Finset (Fin n × Fin n) :=
  (Set.toFinite {uv : Fin n × Fin n |
    uv.1 < uv.2 ∧ 2 ≤ (rowSupport S uv.1 ∩ rowSupport S uv.2).card}).toFinset

/-- Total number `∑_{1 ≤ u < v ≤ n} 1{|supp(s_u) ∩ supp(s_v)| ≥ 2}` of distinct row pairs of `S`
sharing at least two non-zero column coordinates. -/
noncomputable def overlapPairCount {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) : ℕ :=
  (overlapPairs S).card

/-- **Definition 1.2 (Overlap condition, p. 3):** `S ∈ ℝ^{n×k}` satisfies the overlap condition
with parameter `η` if `∑_{1 ≤ u < v ≤ n} 1{|supp(s_u) ∩ supp(s_v)| ≥ 2} ≤ η · n² / k`. -/
def SatisfiesOverlapCond {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (η : ℝ) : Prop :=
  (overlapPairCount S : ℝ) ≤ η * ((n : ℝ) ^ 2 / (k : ℝ))

/-- Entrywise Borel measurability of a random matrix `M : Ω_prob → ℝ^{n×k}` on a measurable space
`Ω_prob`. -/
def IsRandomMatrix {Ω_prob : Type} [MeasurableSpace Ω_prob] {n k : ℕ}
    (M : Ω_prob → Matrix (Fin n) (Fin k) ℝ) : Prop :=
  ∀ (i : Fin n) (j : Fin k), Measurable (fun ω => M ω i j)

/-- Isotropy `E[Ω Ωᵀ] = I_n` (Section 1.1, p. 3): every entry of `Ω Ωᵀ` is integrable under `P`
and has expectation equal to `(I_n)_{i,j}`. -/
def IsIsotropic {Ω_prob : Type} [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob)
    {n k : ℕ} (M : Ω_prob → Matrix (Fin n) (Fin k) ℝ) : Prop :=
  (∀ (i j : Fin n), MeasureTheory.Integrable (fun ω => (M ω * (M ω).transpose) i j) P) ∧
    ∀ (i j : Fin n),
      (∫ ω, (M ω * (M ω).transpose) i j ∂P) = (1 : Matrix (Fin n) (Fin n) ℝ) i j

/-- Almost-sure row sparsity `ζ`: with `P`-probability `1`, every row `i ∈ [n]` of `M ω` has at
most `ζ` non-zero entries. -/
def IsRowSparse {Ω_prob : Type} [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob)
    {n k : ℕ} (M : Ω_prob → Matrix (Fin n) (Fin k) ℝ) (ζ : ℕ) : Prop :=
  ∀ᵐ ω ∂P, ∀ i : Fin n, (rowSupport (M ω) i).card ≤ ζ

/-- `M` satisfies the overlap condition (Definition 1.2) with parameter `η` with `P`-probability
at least `p_ov`. -/
def SatisfiesOverlapWhp {Ω_prob : Type} [MeasurableSpace Ω_prob]
    (P : MeasureTheory.Measure Ω_prob) {n k : ℕ} (M : Ω_prob → Matrix (Fin n) (Fin k) ℝ)
    (η p_ov : ℝ) : Prop :=
  p_ov ≤ (P {ω : Ω_prob | SatisfiesOverlapCond (M ω) η}).toReal

/-- `(r, α)`-oblivious subspace injection with success probability `p_osi`: for every fixed
isometry `Q ∈ ℝ^{n×r}` (`Qᵀ Q = I_r`), `P(σ_min(Ωᵀ Q)² ≥ α) ≥ p_osi`. -/
def IsOSIWithProb {Ω_prob : Type} [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob)
    {n k : ℕ} (M : Ω_prob → Matrix (Fin n) (Fin k) ℝ) (r : ℕ) (α p_osi : ℝ) : Prop :=
  ∀ Q : Matrix (Fin n) (Fin r) ℝ, IsIsometry Q →
    p_osi ≤ (P {ω : Ω_prob | MinEigenvalueAtLeast ((M ω).transpose * Q) α}).toReal

/-- Canonical `(r, α)`-oblivious subspace injection with success probability `19/20`
(Theorem 1.1, p. 3 & p. 34; Lemma 10.1 proof, p. 46). -/
def IsOSI {Ω_prob : Type} [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob)
    {n k : ℕ} (M : Ω_prob → Matrix (Fin n) (Fin k) ℝ) (r : ℕ) (α : ℝ) : Prop :=
  IsOSIWithProb P M r α (19 / 20)

/-! ## 3. Finite uniform laws and the SparseStack ensemble -/

/-- Uniform probability `#{ω | E ω} / #S` on a finite sample space `S`. -/
noncomputable def uniformProb (S : Type) [Fintype S] (E : S → Prop) : ℝ :=
  (Nat.card {ω : S // E ω} : ℝ) / (Fintype.card S : ℝ)

/-- Uniform expectation `(1 / #S) ∑_ω f(ω)` of a real-valued function on a finite sample space. -/
noncomputable def uniformMeanReal (S : Type) [Fintype S] (f : S → ℝ) : ℝ :=
  (Fintype.card S : ℝ)⁻¹ * ∑ ω : S, f ω

/-- Uniform expectation `(1 / #S) ∑_ω f(ω)` of a matrix-valued function on a finite sample space. -/
noncomputable def uniformMeanMatrix {S : Type} [Fintype S] {m l : Type}
    (f : S → Matrix m l ℝ) : Matrix m l ℝ :=
  (Fintype.card S : ℝ)⁻¹ • ∑ ω : S, f ω

/-- Uniform probability over `r`-element subsets `R ∈ ([n] choose r)`. -/
noncomputable def uniformSubsetProb (n r : ℕ) (E : Finset (Fin n) → Prop) : ℝ :=
  (((Set.toFinite {R : Finset (Fin n) | R.card = r ∧ E R}).toFinset).card : ℝ) /
    (Nat.choose n r : ℝ)

/-- Rademacher sign `±1` encoded by a `Bool` (`true ↦ 1`, `false ↦ -1`). -/
def signValue (β : Bool) : ℝ :=
  if β then 1 else -1

/-- Sample space of a `ζ`-block, `b`-bucket SparseStack on `n` input rows: independent bucket
indices `h t i ∈ Fin b` and sign bits `σ t i ∈ Bool` across all `t ∈ Fin ζ` and `i ∈ Fin n`. -/
abbrev SketchSample (ζ b n : ℕ) : Type :=
  (Fin ζ → Fin n → Fin b) × (Fin ζ → Fin n → Bool)

/-- The `n × (ζ·b)` SparseStack matrix `Ω_{ζ,b} ∈ ℝ^{n × (ζ·b)}`: column `j` corresponds via
`finProdFinEquiv` to `(t, u) ∈ Fin ζ × Fin b`, with entry `ζ^{-1/2} σ_{t,i} [h_t(i) = u]`. -/
noncomputable def sparseStackOmega {ζ b n : ℕ} (ω : SketchSample ζ b n) :
    Matrix (Fin n) (Fin (ζ * b)) ℝ :=
  fun i j =>
    let p := finProdFinEquiv.symm j
    (Real.sqrt (ζ : ℝ))⁻¹ * (if ω.1 p.1 i = p.2 then signValue (ω.2 p.1 i) else 0)

/-- The uniform probability measure on `SketchSample ζ b n` (as a `MeasureTheory.Measure`). -/
noncomputable def sparseStackMeasure (ζ b n : ℕ) :
    MeasureTheory.Measure (SketchSample ζ b n) :=
  ((Fintype.card (SketchSample ζ b n) : ENNReal)⁻¹) •
    ∑ ω : SketchSample ζ b n, MeasureTheory.Measure.dirac ω

/-- Explicit universal constant `C = 32768` of Theorem 1.1. -/
def constC : ℕ := 32768

/-- Explicit universal constant `K = 160000000` of Theorem 1.1. -/
def constK : ℕ := 160000000

/-- Explicit universal constant `α = 12256937 / 119880000000 > 10⁻⁴` of Theorem 1.1. -/
noncomputable def constAlpha : ℝ := 12256937 / 119880000000

/-- Canonical block schedule `ζ(r) = ⌈C √log(e r)⌉`. -/
noncomputable def numBlocks (r : ℕ) : ℕ :=
  Nat.ceil ((constC : ℝ) * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))))

/-- Canonical bucket schedule `b(r) = ⌈K r / ζ(r)⌉`. -/
noncomputable def numBuckets (r : ℕ) : ℕ :=
  Nat.ceil ((constK : ℝ) * (r : ℝ) / (numBlocks r : ℝ))

/-! ## 4. Section 1.1 Main Results & Shared-Vocabulary Tightness -/

/-- **Theorem 1.1 (General `(ζ, b)` form, pp. 1, 3, 34):** For `C = constC`, `K = constK`, and
`α = constAlpha ∈ (10⁻⁴, 1)`, for all `n ≥ r ≥ 2` and all integer parameters `ζ, b` satisfying
`ζ ≥ C √log(e r)`, `b ≥ 2`, and `k = ζ b ≥ K r`, the SparseStack sketch `Ω_{ζ,b}` is an isotropic
`(r, α)`-oblivious subspace injection (with probability at least `19/20`). -/
def Theorem_1_1_GeneralParams : Prop :=
  (1 / 10000 : ℝ) < constAlpha ∧ constAlpha < 1 ∧
    ∀ (n r ζ b : ℕ), 2 ≤ r → r ≤ n → 2 ≤ b →
      (constC : ℝ) * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))) ≤ (ζ : ℝ) →
      constK * r ≤ ζ * b →
      MeasureTheory.IsProbabilityMeasure (sparseStackMeasure ζ b n) ∧
        IsRandomMatrix (sparseStackOmega (ζ := ζ) (b := b) (n := n)) ∧
        IsIsotropic (sparseStackMeasure ζ b n)
          (sparseStackOmega (ζ := ζ) (b := b) (n := n)) ∧
        IsRowSparse (sparseStackMeasure ζ b n)
          (sparseStackOmega (ζ := ζ) (b := b) (n := n)) ζ ∧
        IsOSI (sparseStackMeasure ζ b n)
          (sparseStackOmega (ζ := ζ) (b := b) (n := n)) r constAlpha ∧
        ∀ Q : Matrix (Fin n) (Fin r) ℝ, IsIsometry Q →
          (19 / 20 : ℝ) ≤ uniformProb (SketchSample ζ b n)
            (fun ω => MinEigenvalueAtLeast ((sparseStackOmega ω).transpose * Q) constAlpha)

/-- **Theorem 1.1 (Existential universal-constant `Θ(√log r)` / `Θ(r)` form, pp. 1, 3):**
There exist universal constants `C, K > 0` and `α ∈ (0, 1)` such that for every `n ≥ r ≥ 2` and
every `C_up ≥ 2 C`, there exist integers `ζ, b ≥ 2` with `C √log(e r) ≤ ζ ≤ C_up √log(e r)` and
`K r ≤ ζ b ≤ 2 K r` for which `SparseStack(ζ, b, n)` is an isotropic `(r, α)`-OSI. -/
def Theorem_1_1_PaperRange : Prop :=
  ∃ (C K α : ℝ), 0 < C ∧ 0 < K ∧ 0 < α ∧ α < 1 ∧
    ∀ (n r : ℕ), 2 ≤ r → r ≤ n →
      ∀ C_up : ℝ, 2 * C ≤ C_up →
        ∃ (ζ b : ℕ), 2 ≤ b ∧
          C * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))) ≤ (ζ : ℝ) ∧
          (ζ : ℝ) ≤ C_up * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))) ∧
          K * (r : ℝ) ≤ ((ζ * b : ℕ) : ℝ) ∧
          ((ζ * b : ℕ) : ℝ) ≤ 2 * K * (r : ℝ) ∧
          MeasureTheory.IsProbabilityMeasure (sparseStackMeasure ζ b n) ∧
          IsIsotropic (sparseStackMeasure ζ b n)
            (sparseStackOmega (ζ := ζ) (b := b) (n := n)) ∧
          IsRowSparse (sparseStackMeasure ζ b n)
            (sparseStackOmega (ζ := ζ) (b := b) (n := n)) ζ ∧
          IsOSI (sparseStackMeasure ζ b n)
            (sparseStackOmega (ζ := ζ) (b := b) (n := n)) r α

/-- **Theorem 1.1 (Canonical schedule `ζ = numBlocks r`, `b = numBuckets r`, pp. 34–36):**
Includes the probability bound (`≥ 19/20`), exact isotropy `E[Ω Ωᵀ] = I_n`, linear sketch
dimension `ζ b ≤ K r + ζ ≤ (K + C + 1) r`, and `α > 10⁻⁴`. -/
def Theorem_1_1_Schedule : Prop :=
  (1 / 10000 : ℝ) < constAlpha ∧ constAlpha < 1 ∧
    (∀ r : ℕ, 2 ≤ r →
      numBuckets r * numBlocks r ≤ constK * r + numBlocks r ∧
        constK * r + numBlocks r ≤ (constK + constC + 1) * r) ∧
    ∀ (n r : ℕ), 2 ≤ r → r ≤ n →
      uniformMeanMatrix
          (fun ω : SketchSample (numBlocks r) (numBuckets r) n =>
            sparseStackOmega ω * (sparseStackOmega ω).transpose) = 1 ∧
        ∀ Q : Matrix (Fin n) (Fin r) ℝ, IsIsometry Q →
          (19 / 20 : ℝ) ≤ uniformProb (SketchSample (numBlocks r) (numBuckets r) n)
            (fun ω => MinEigenvalueAtLeast ((sparseStackOmega ω).transpose * Q) constAlpha)

/-- **Proposition (SparseStack satisfies Definition 1.2, Section 1.1, pp. 3–4):**
For all `n : ℕ` and `ζ, b ≥ 1` (with `k = ζ b`), `SparseStack(ζ, b, n)` satisfies Definition 1.2
with overlap parameter `η = 5 ζ⁴ / (2 k) = O(ζ⁴ / k)` with probability at least `9/10`. -/
def Proposition_SparseStack_Overlap : Prop :=
  ∀ (n ζ b : ℕ), 1 ≤ ζ → 1 ≤ b →
    SatisfiesOverlapWhp (sparseStackMeasure ζ b n)
      (sparseStackOmega (ζ := ζ) (b := b) (n := n))
      (5 * (ζ : ℝ) ^ 4 / (2 * ((ζ * b : ℕ) : ℝ))) (9 / 10) ∧
    (9 / 10 : ℝ) ≤ uniformProb (SketchSample ζ b n)
      (fun ω => SatisfiesOverlapCond (sparseStackOmega ω)
        (5 * (ζ : ℝ) ^ 4 / (2 * ((ζ * b : ℕ) : ℝ))))

/-- **Theorem 1.3 (Strong `1/2`-probability lower bound, p. 4 & Theorem 10.2, p. 46):**
For every `K ≥ 1` and `α ∈ (0, 1)`, there exist constants `c > 0`, `C_H > 0`, `C_n > 0`, and
`r₀ ≥ 3` such that for all `r ≥ r₀`, all `n ≥ r` with `n ≥ C_n r (log r / log log r)³`, all
`k ≤ K r`, and all `ζ : ℕ`, any isotropic random matrix `M : Ω_prob → ℝ^{n×k}` with row sparsity
`ζ` satisfying Definition 1.2 at `η = (C_H ζ⁶)⁻¹` w.p. `≥ 9/10` and `(r, α)`-OSI w.p. `≥ 1/2`
must satisfy `ζ ≥ c √(log r / log log r)`. -/
def Theorem_1_3_LowerBound_HalfProb : Prop :=
  ∀ (K α : ℝ), 1 ≤ K → 0 < α → α < 1 →
    ∃ (c C_H C_n : ℝ) (r₀ : ℕ), 0 < c ∧ 0 < C_H ∧ 0 < C_n ∧ 3 ≤ r₀ ∧
      ∀ (n r k ζ : ℕ), r₀ ≤ r → r ≤ n →
        C_n * (r : ℝ) * (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 ≤ (n : ℝ) →
        (k : ℝ) ≤ K * (r : ℝ) →
        ∀ (Ω_prob : Type) [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob),
          MeasureTheory.IsProbabilityMeasure P →
          ∀ M : Ω_prob → Matrix (Fin n) (Fin k) ℝ,
            IsRandomMatrix M →
            IsIsotropic P M →
            IsRowSparse P M ζ →
            SatisfiesOverlapWhp P M ((C_H * (ζ : ℝ) ^ 6)⁻¹) (9 / 10) →
            IsOSIWithProb P M r α (1 / 2) →
            c * Real.sqrt (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ≤ (ζ : ℝ)

/-- **Theorem 1.3 (Paper `19/20`-OSI lower bound, p. 4):**
Same statement under the canonical `IsOSI` (`19/20` success probability) predicate. -/
def Theorem_1_3_LowerBound : Prop :=
  ∀ (K α : ℝ), 1 ≤ K → 0 < α → α < 1 →
    ∃ (c C_H C_n : ℝ) (r₀ : ℕ), 0 < c ∧ 0 < C_H ∧ 0 < C_n ∧ 3 ≤ r₀ ∧
      ∀ (n r k ζ : ℕ), r₀ ≤ r → r ≤ n →
        C_n * (r : ℝ) * (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 ≤ (n : ℝ) →
        (k : ℝ) ≤ K * (r : ℝ) →
        ∀ (Ω_prob : Type) [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob),
          MeasureTheory.IsProbabilityMeasure P →
          ∀ M : Ω_prob → Matrix (Fin n) (Fin k) ℝ,
            IsRandomMatrix M →
            IsIsotropic P M →
            IsRowSparse P M ζ →
            SatisfiesOverlapWhp P M ((C_H * (ζ : ℝ) ^ 6)⁻¹) (9 / 10) →
            IsOSI P M r α →
            c * Real.sqrt (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ≤ (ζ : ℝ)

/-- **Theorem 1.3 (Quadratic ambient dimension `n ≥ 100 r²`, matching `[NN13]`, p. 4):** -/
def Theorem_1_3_QuadraticN : Prop :=
  ∀ (K α : ℝ), 1 ≤ K → 0 < α → α < 1 →
    ∃ (c C_H : ℝ) (r₀ : ℕ), 0 < c ∧ 0 < C_H ∧ 3 ≤ r₀ ∧
      ∀ (n r k ζ : ℕ), r₀ ≤ r → 100 * r ^ 2 ≤ n → (k : ℝ) ≤ K * (r : ℝ) →
        ∀ (Ω_prob : Type) [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob),
          MeasureTheory.IsProbabilityMeasure P →
          ∀ M : Ω_prob → Matrix (Fin n) (Fin k) ℝ,
            IsRandomMatrix M →
            IsIsotropic P M →
            IsRowSparse P M ζ →
            SatisfiesOverlapWhp P M ((C_H * (ζ : ℝ) ^ 6)⁻¹) (9 / 10) →
            IsOSI P M r α →
            c * Real.sqrt (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ≤ (ζ : ℝ)

/-- **Necessity of an ambient-dimension lower bound (`n > K r`) in Theorem 1.3 / Theorem 10.2:**
Whenever `2 ≤ r ≤ n` and `n ≤ K r`, the deterministic identity matrix `Ω = I_n ∈ ℝ^{n×n}`
(`k = n ≤ K r`) on the point probability space `(PUnit, dirac ())` satisfies `IsRandomMatrix`,
`IsIsotropic`, `IsRowSparse` with `ζ = 1`, `SatisfiesOverlapWhp` with `η = 0` w.p. `1`, and
`IsOSIWithProb` with `α ≤ 1` w.p. `1` (hence `IsOSI`), achieving constant sparsity `ζ = 1`. -/
def Theorem_1_3_NecessityOfAmbientBound : Prop :=
  ∀ (K α : ℝ), 1 ≤ K → 0 < α → α ≤ 1 →
    ∀ (n r : ℕ), 2 ≤ r → r ≤ n → (n : ℝ) ≤ K * (r : ℝ) →
      let P : MeasureTheory.Measure PUnit := MeasureTheory.Measure.dirac PUnit.unit
      let M : PUnit → Matrix (Fin n) (Fin n) ℝ := fun _ => 1
      MeasureTheory.IsProbabilityMeasure P ∧
        ((n : ℝ) ≤ K * (r : ℝ)) ∧
        IsRandomMatrix M ∧
        IsIsotropic P M ∧
        IsRowSparse P M 1 ∧
        (∀ η : ℝ, 0 ≤ η → SatisfiesOverlapWhp P M η 1) ∧
        IsOSIWithProb P M r α 1 ∧
        IsOSI P M r α

/-- **Unified Optimal Tightness of SparseStack (Shared-Vocabulary Bridge, Section 1.1):**
At linear sketch dimension `k ≤ K_tot r` (`K_tot = constK + constC + 1`) and distortion
`α = constAlpha`:
1. (**Upper bound in the exact lower-bound model**) For all `r ≥ r₀` and `n ≥ 100 r²`,
   `SparseStack(numBlocks r, numBuckets r, n)` satisfies `IsProbabilityMeasure`, `IsRandomMatrix`,
   `IsIsotropic`, `IsRowSparse _ _ (numBlocks r)`, `SatisfiesOverlapWhp _ _ ((C_H · ζ⁶)⁻¹) (9/10)`,
   and `IsOSI _ _ r constAlpha`, with `numBlocks r ≤ 2 constC √log(e r)`.
2. (**Matching lower bound under the identical predicates**) Every random matrix `(Ω_prob, P, M)`
   in `ℝ^{n×k}` (`k ≤ K_tot r`) satisfying those exact same predicates must have
   `ζ ≥ c √(log r / log log r)`. -/
def Theorem_Optimal_SparseStack_Tightness : Prop :=
  let K_tot : ℝ := (constK + constC + 1 : ℕ)
  ∃ (c C_H : ℝ) (r₀ : ℕ), 0 < c ∧ 0 < C_H ∧ 3 ≤ r₀ ∧
    (∀ (n r : ℕ), r₀ ≤ r → 100 * r ^ 2 ≤ n →
      let ζ := numBlocks r
      let b := numBuckets r
      (((ζ * b : ℕ) : ℝ) ≤ K_tot * (r : ℝ)) ∧
        ((ζ : ℝ) ≤ 2 * (constC : ℝ) * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ)))) ∧
        MeasureTheory.IsProbabilityMeasure (sparseStackMeasure ζ b n) ∧
        IsRandomMatrix (sparseStackOmega (ζ := ζ) (b := b) (n := n)) ∧
        IsIsotropic (sparseStackMeasure ζ b n)
          (sparseStackOmega (ζ := ζ) (b := b) (n := n)) ∧
        IsRowSparse (sparseStackMeasure ζ b n)
          (sparseStackOmega (ζ := ζ) (b := b) (n := n)) ζ ∧
        SatisfiesOverlapWhp (sparseStackMeasure ζ b n)
          (sparseStackOmega (ζ := ζ) (b := b) (n := n))
          ((C_H * (ζ : ℝ) ^ 6)⁻¹) (9 / 10) ∧
        IsOSI (sparseStackMeasure ζ b n)
          (sparseStackOmega (ζ := ζ) (b := b) (n := n)) r constAlpha) ∧
    (∀ (n r k ζ : ℕ), r₀ ≤ r → 100 * r ^ 2 ≤ n → (k : ℝ) ≤ K_tot * (r : ℝ) →
      ∀ (Ω_prob : Type) [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob),
        MeasureTheory.IsProbabilityMeasure P →
        ∀ M : Ω_prob → Matrix (Fin n) (Fin k) ℝ,
          IsRandomMatrix M →
          IsIsotropic P M →
          IsRowSparse P M ζ →
          SatisfiesOverlapWhp P M ((C_H * (ζ : ℝ) ^ 6)⁻¹) (9 / 10) →
          IsOSI P M r constAlpha →
          c * Real.sqrt (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ≤ (ζ : ℝ))

/-! ## 5. Sections 2–6 Upper-Bound Pipeline Definitions & Statements -/

/-- Entry encoding for the independent-entry `{±1, 0}` model of Fact 5.1 (p. 24): on `Fin (2B)`
(`B ≥ 2`), `0 ↦ +1`, `1 ↦ -1`, and `u ≥ 2 ↦ 0` (probabilities `1/(2B), 1/(2B), 1 - 1/B`). -/
def iidTernaryEntry {B : ℕ} (u : Fin (2 * B)) : ℝ :=
  if u.val = 0 then 1 else if u.val = 1 then -1 else 0

/-- Sample space for an `m × n` independent-entry `{±1, 0}` matrix with non-zero probability `1/B`
(Fact 5.1 & Lemma 5.3, pp. 24–25). -/
abbrev IidTernarySample (m n B : ℕ) : Type :=
  Fin m → Fin n → Fin (2 * B)

/-- Matrix `X ∈ {-1, 0, 1}^{m×n}` associated with `ω ∈ IidTernarySample m n B`. -/
def iidTernaryMatrix {m n B : ℕ} (ω : IidTernarySample m n B) : Matrix (Fin m) (Fin n) ℝ :=
  fun ℓ j => iidTernaryEntry (ω ℓ j)

/-- Number of coordinates of `I` hashed to bucket `u` in block `t` of `ω`. -/
def bucketLoad {ζ b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample ζ b n)
    (t : Fin ζ) (u : Fin b) : ℕ :=
  (I.filter (fun i => ω.1 t i = u)).card

/-- Number of blocks `t ∈ [ζ]` in which `i ∈ [n]` lands in a bucket containing no other coordinate
of `I` (`a_i` in Lemmas 6.1 and 6.2, pp. 30–31). -/
def isolatedBlockCount {ζ b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample ζ b n)
    (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun t : Fin ζ => ∀ j ∈ I, j ≠ i → ω.1 t j ≠ ω.1 t i)).card

/-- Diagonal selector matrix on `Fin (ζ * b)` retaining output coordinates `(t, u)` that contain
exactly one element of `I` (`T` in Lemma 5.4, p. 27). -/
def retainUniqueMatrix {ζ b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample ζ b n) :
    Matrix (Fin (ζ * b)) (Fin (ζ * b)) ℝ :=
  Matrix.diagonal (fun j =>
    let p := finProdFinEquiv.symm j
    if bucketLoad I ω p.1 p.2 = 1 then 1 else 0)

/-- Head-background sample merge: coordinates in `I` (all blocks and signs) come from `ω₀`, while
coordinates outside `I` come from `ω` (used to express conditioning on `Ω_{ζ,b,I}` in Lemmas 5.4
and 6.1). -/
def mergeHeadSample {ζ b n : ℕ} (I : Finset (Fin n)) (ω₀ ω : SketchSample ζ b n) :
    SketchSample ζ b n :=
  (fun t i => if i ∈ I then ω₀.1 t i else ω.1 t i,
   fun t i => if i ∈ I then ω₀.2 t i else ω.2 t i)

/-- Retained cross-term matrix `H̃ᵀ Ỹ` on `ℝ^n × ℝ^d` (with zero rows outside `I`, matching the
operator norm of the `|I| × d` matrix `(T Ω_{ζ,b,I}ᵀ)ᵀ (T Ω_{ζ,b,J}ᵀ W)` of Lemma 5.4, p. 27). -/
noncomputable def retainedCrossGram {ζ b n d : ℕ} (I : Finset (Fin n))
    (V : Matrix (Fin n) (Fin d) ℝ) (ω : SketchSample ζ b n) : Matrix (Fin n) (Fin d) ℝ :=
  let T := retainUniqueMatrix I ω
  let Phi := (sparseStackOmega ω).transpose
  (T * Phi * Matrix.diagonal (fun i : Fin n => if i ∈ I then (1 : ℝ) else 0)).transpose *
    (T * Phi * V)

/-- **Theorem 2.1 (Uniform preservation of flat vectors, pp. 7, 19):**
There exists a universal constant `c_lam > 0` such that for every `ε ∈ (0, 1)` and `δ_loc ∈ (0, 1)`,
there exist constants `λ ≥ c_lam ε`, `Θ ≥ 1`, `M_loc ≥ 1`, and `r₀ ≥ 1` such that for all
`n ≥ r ≥ r₀`, `1 ≤ ζ ≤ r`, `b ≥ 1`, `ζ b ≥ Θ r`, `m ≥ M_loc r / ζ`, and every isometry
`Q ∈ ℝ^{n×r}`, `P(∃ x ∈ S^{r-1}, d_m(Q x) ≥ ε ∧ ‖Ωᵀ Q x‖ < λ) ≤ δ_loc`. -/
def Theorem_2_1_FlatPreservation : Prop :=
  ∃ c_lam : ℝ, 0 < c_lam ∧
    ∀ (ε δ_loc : ℝ), 0 < ε → ε < 1 → 0 < δ_loc → δ_loc < 1 →
      ∃ (lam Θ M_loc : ℝ) (r₀ : ℕ), c_lam * ε ≤ lam ∧ 1 ≤ Θ ∧ 1 ≤ M_loc ∧ 1 ≤ r₀ ∧
        ∀ (n r ζ b m : ℕ), r₀ ≤ r → r ≤ n → 1 ≤ ζ → ζ ≤ r → 1 ≤ b →
          Θ * (r : ℝ) ≤ ((ζ * b : ℕ) : ℝ) →
          M_loc * (r : ℝ) ≤ (ζ : ℝ) * (m : ℝ) →
          ∀ Q : Matrix (Fin n) (Fin r) ℝ, IsIsometry Q →
            uniformProb (SketchSample ζ b n)
              (fun ω => ∃ x : Fin r → ℝ,
                vecSqNorm x = 1 ∧ ε ^ 2 ≤ distSparseSq m (Q.mulVec x) ∧
                  vecSqNorm (((sparseStackOmega ω).transpose * Q).mulVec x) < lam ^ 2) ≤ δ_loc

/-- **Theorem 2.2 (Common support extraction for spiky vectors, pp. 8, 22):**
If `Q ∈ ℝ^{n×r}` is an isometry, `m ≥ 1`, `ε > 0`, `λ > 0`, and `X ∈ ℝ^{k×r}` satisfies
`d_m(Q x) ≥ ε ∧ ‖x‖ = 1 ⇒ ‖X x‖ ≥ λ`, then there exists `I ⊆ [n]` with `|I| ≤ 8 m` such that
`Q_{Iᶜ}ᵀ Q_{Iᶜ} ⪯ (8/3) ε² I_r + (8 / (3 λ²)) Xᵀ X`. -/
def Theorem_2_2_CommonSupport : Prop :=
  ∀ (n r k m : ℕ) (ε lam : ℝ), 1 ≤ m → 0 < ε → 0 < lam →
    ∀ (Q : Matrix (Fin n) (Fin r) ℝ) (X : Matrix (Fin k) (Fin r) ℝ),
      IsIsometry Q →
      (∀ x : Fin r → ℝ, vecSqNorm x = 1 → ε ^ 2 ≤ distSparseSq m (Q.mulVec x) →
        lam ^ 2 ≤ vecSqNorm (X.mulVec x)) →
      ∃ I : Finset (Fin n), I.card ≤ 8 * m ∧
        LoewnerLe ((coordRows Iᶜ Q).transpose * coordRows Iᶜ Q)
          (((8 / 3 : ℝ) * ε ^ 2) • (1 : Matrix (Fin r) (Fin r) ℝ) +
            ((8 / (3 * lam ^ 2) : ℝ) • (X.transpose * X)))

/-- **Theorem 2.3 (End-to-end heavy-coordinate preservation, pp. 9, 33):**
For every `t₀ ∈ (0, 1/4)` and `δ_rep ∈ (0, 1)`, there exist constants
`β ≥ (1/3)(11/12 - 2 t₀) > 0`, `C⋆ > 0`, and `K⋆ > 0` such that for all `n ≥ r ≥ 2`,
`ζ ≥ C⋆ √log(e r)`, `k = ζ b ≥ K⋆ r`, every isometry `Q ∈ ℝ^{n×r}`, and every `I ⊆ [n]` with
`|I| ≤ min{r, b / 16}`, `Y = Ω_{ζ,b}ᵀ Q` satisfies with probability at least `1 - δ_rep` both
`‖Y x‖² ≥ β ‖(Q x)_I‖² - t₀ ‖(Q x)_{Iᶜ}‖²` for all `x ∈ ℝ^r` and equivalently
`Yᵀ Y + (β + t₀) Q_{Iᶜ}ᵀ Q_{Iᶜ} ⪰ β I_r`. -/
def Theorem_2_3_HeavyPreservation : Prop :=
  ∀ (t₀ δ_rep : ℝ), 0 < t₀ → t₀ < 1 / 4 → 0 < δ_rep → δ_rep < 1 →
    ∃ (β C_star K_star : ℝ),
      (1 / 3 : ℝ) * (11 / 12 - 2 * t₀) ≤ β ∧ 0 < C_star ∧ 0 < K_star ∧
      ∀ (n r ζ b : ℕ), 2 ≤ r → r ≤ n →
        C_star * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))) ≤ (ζ : ℝ) →
        K_star * (r : ℝ) ≤ ((ζ * b : ℕ) : ℝ) →
        ∀ (Q : Matrix (Fin n) (Fin r) ℝ) (I : Finset (Fin n)),
          IsIsometry Q → I.card ≤ r → 16 * I.card ≤ b →
          (1 - δ_rep) ≤ uniformProb (SketchSample ζ b n)
            (fun ω =>
              let Y := (sparseStackOmega ω).transpose * Q
              (∀ x : Fin r → ℝ,
                β * vecSqNorm (coordVec I (Q.mulVec x)) -
                    t₀ * vecSqNorm (coordVec Iᶜ (Q.mulVec x)) ≤
                  vecSqNorm (Y.mulVec x)) ∧
                LoewnerLe (β • (1 : Matrix (Fin r) (Fin r) ℝ))
                  (Y.transpose * Y +
                    (β + t₀) • ((coordRows Iᶜ Q).transpose * coordRows Iᶜ Q)))

/-- **Lemma 3.2 (Weighted Bernoulli lower tail, p. 16):**
For independent `{0, 1}`-valued random variables `B_j` with `P(B_j = 1) ≥ p₀ > 0` and weights
`0 ≤ v_j ≤ v_max` (`v_max > 0`, `V₀ = ∑_j v_j > 0`), there exist `c₁, c₂ > 0` depending only on
`p₀` such that `P(∑_j v_j B_j < c₁ V₀) ≤ exp(- c₂ V₀ / v_max)`. -/
def Lemma_3_2_WeightedBernoulli : Prop :=
  ∀ p₀ : ℝ, 0 < p₀ →
    ∃ (c₁ c₂ : ℝ), 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (m : ℕ) (Ω_prob : Type) [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob),
        MeasureTheory.IsProbabilityMeasure P →
        ∀ (B : Fin m → Ω_prob → ℝ) (v : Fin m → ℝ) (v_max : ℝ),
          ProbabilityTheory.iIndepFun B P →
          (∀ j : Fin m, Measurable (B j)) →
          (∀ (j : Fin m) (ω : Ω_prob), B j ω = 0 ∨ B j ω = 1) →
          (∀ j : Fin m, p₀ ≤ (P {ω : Ω_prob | B j ω = 1}).toReal) →
          (∀ j : Fin m, 0 ≤ v j ∧ v j ≤ v_max) →
          0 < v_max →
          0 < (∑ j : Fin m, v j) →
          (P {ω : Ω_prob |
            (∑ j : Fin m, v j * B j ω) < c₁ * (∑ j : Fin m, v j)}).toReal ≤
            Real.exp (-c₂ * (∑ j : Fin m, v j) / v_max)

/-- **Lemma 3.3 (Pointwise lower bound for flat tail vectors, p. 17):**
There exist universal constants `c₀, c_sb > 0` such that for any `h, z ∈ ℝ^n` with disjoint
supports, `a > 0`, `‖z‖₂ = 1`, `1 ≤ D ≤ b`, and `‖z‖_∞² ≤ D⁻¹`, a `ζ`-block SparseStack satisfies
`P(‖Ω_{ζ,b}ᵀ (h + a z)‖₂ < c₀ a) ≤ 2 exp(- c_sb ζ D)`. -/
def Lemma_3_3_PointwiseFlat : Prop :=
  ∃ (c₀ c_sb : ℝ), 0 < c₀ ∧ 0 < c_sb ∧
    ∀ (ζ b n : ℕ) (h z : Fin n → ℝ) (a D : ℝ),
      1 ≤ ζ → 1 ≤ b → 0 < a →
      (∀ i : Fin n, h i = 0 ∨ z i = 0) →
      vecSqNorm z = 1 →
      1 ≤ D → D ≤ (b : ℝ) →
      (∀ i : Fin n, (z i) ^ 2 ≤ D⁻¹) →
      uniformProb (SketchSample ζ b n)
        (fun ω => vecSqNorm ((sparseStackOmega ω).transpose.mulVec (h + a • z)) < (c₀ * a) ^ 2) ≤
        2 * Real.exp (-c_sb * (ζ : ℝ) * D)

/-- **Lemma 3.4 (Unbiased lattice rounding net, p. 18):**
For every `r ≥ 1` and `0 < η < 1`, there exists a finite set `N_η ⊂ (1 + η) B₂^r` of cardinality
`|N_η| ≤ (16 / η)^r` such that for every real matrix `T ∈ ℝ^{k×r}` and every unit vector
`x ∈ S^{r-1}`, some `y ∈ N_η` satisfies `‖x - y‖₂ ≤ η` and `‖T(x - y)‖₂² ≤ (η² / (4 r)) ‖T‖_F²`. -/
def Lemma_3_4_LatticeRounding : Prop :=
  ∀ (r : ℕ) (η : ℝ), 1 ≤ r → 0 < η → η < 1 →
    ∃ N_net : Finset (Fin r → ℝ),
      (N_net.card : ℝ) ≤ (16 / η) ^ r ∧
        (∀ y ∈ N_net, vecSqNorm y ≤ (1 + η) ^ 2) ∧
        ∀ (k : ℕ) (T : Matrix (Fin k) (Fin r) ℝ) (x : Fin r → ℝ),
          vecSqNorm x = 1 →
          ∃ y ∈ N_net,
            vecSqNorm (x - y) ≤ η ^ 2 ∧
              vecSqNorm (T.mulVec (x - y)) ≤ (η ^ 2 / (4 * (r : ℝ))) * frobSq T

/-- **Lemma 4.1 (Truncation lower bound for Gaussian / fourth-moment vectors, p. 21):**
For any random vector `g : Ω_prob → ℝ^n` (`n > 4 m`) whose coordinates have finite fourth moments
satisfying the Gaussian marginal bound `E[gᵢ⁴] ≤ 3 (E[gᵢ²])²` (which holds with equality for any
centered Gaussian vector `g`), if `σ` sorts `aᵢ = E[gᵢ²]` in non-increasing order, then
`E[d_m(g)²] ≥ (3/4) ∑_{i > 4m} a_{σ(i)}`. -/
def Lemma_4_1_GaussianTruncation : Prop :=
  ∀ (n m : ℕ), 4 * m < n →
    ∀ (Ω_prob : Type) [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob),
      MeasureTheory.IsProbabilityMeasure P →
      ∀ g : Ω_prob → Fin n → ℝ,
        (∀ i : Fin n, Measurable (fun ω => g ω i)) →
        (∀ i : Fin n, MeasureTheory.Integrable (fun ω => (g ω i) ^ 2) P) →
        (∀ i : Fin n, MeasureTheory.Integrable (fun ω => (g ω i) ^ 4) P) →
        (∀ i : Fin n,
          (∫ ω, (g ω i) ^ 4 ∂P) ≤ 3 * (∫ ω, (g ω i) ^ 2 ∂P) ^ 2) →
        ∀ σ : Equiv.Perm (Fin n),
          Antitone (fun i : Fin n => ∫ ω, (g ω (σ i)) ^ 2 ∂P) →
          MeasureTheory.Integrable (fun ω => distSparseSq m (g ω)) P ∧
            (3 / 4 : ℝ) *
                (∑ i : Fin n, if 4 * m ≤ i.val then (∫ ω, (g ω (σ i)) ^ 2 ∂P) else 0) ≤
              ∫ ω, distSparseSq m (g ω) ∂P

/-- **Lemma 4.2 (Minimax extraction of a single common coordinate set, p. 22):**
Let `V ∈ ℝ^{n×r}`, `H ⪰ 0` (`r × r`), and `m ≥ 1`. If `d_m(V x)² ≤ xᵀ H x` for all `x ∈ ℝ^r`,
then there exists `I ⊆ [n]` with `|I| ≤ 8 m` such that `V_{Iᶜ}ᵀ V_{Iᶜ} ⪯ (8/3) H`. -/
def Lemma_4_2_MinimaxSelection : Prop :=
  ∀ (n r m : ℕ), 1 ≤ m →
    ∀ (V : Matrix (Fin n) (Fin r) ℝ) (H : Matrix (Fin r) (Fin r) ℝ),
      H.PosSemidef →
      (∀ x : Fin r → ℝ, distSparseSq m (V.mulVec x) ≤ dotProduct x (H.mulVec x)) →
      ∃ I : Finset (Fin n), I.card ≤ 8 * m ∧
        LoewnerLe ((coordRows Iᶜ V).transpose * coordRows Iᶜ V) ((8 / 3 : ℝ) • H)

/-- **Lemma 5.3 (Expected squared operator norm in the independent-entry model, p. 25):**
There exists an absolute constant `C_ind > 0` such that in Fact 5.1 (`B ≥ 2`, `a ≥ 1`, `m = a B`,
`d ≥ 1`, `W ∈ ℝ^{n×d}` an isometry, `p ≥ max{1, log(2 d)}`, `D_p = d + 2 p + 1`),
`E[‖X W‖²] ≤ C_ind (a + D_p / B + p)`. -/
def Lemma_5_3_IidOpNorm : Prop :=
  ∃ C_ind : ℝ, 0 < C_ind ∧
    ∀ (a B n d p : ℕ), 2 ≤ B → 1 ≤ a → 1 ≤ d → 1 ≤ p →
      Real.log (2 * (d : ℝ)) ≤ (p : ℝ) →
      ∀ W : Matrix (Fin n) (Fin d) ℝ, IsIsometry W →
        uniformMeanReal (IidTernarySample (a * B) n B)
          (fun ω => spectralNorm (iidTernaryMatrix ω * W) ^ 2) ≤
          C_ind * ((a : ℝ) + ((d : ℝ) + 2 * (p : ℝ) + 1) / (B : ℝ) + (p : ℝ))

/-- **Lemma 5.4 (Cross-term operator norm on isolated buckets, p. 27):**
There exists a universal constant `C_cg > 0` such that for `ζ ≥ 1`, `b ≥ 2 ζ`, `I ⊆ [n]` with
`N = |I| ≥ 1`, any fixed isometry `V ∈ ℝ^{n×d}` (`d ≥ 1`) supported off `I`, any integer
`p ≥ max{1, log(2 d)}` (`D_p = d + 2 p + 1`), and any head configuration `ω₀` of `I`,
`E[‖H̃ᵀ Ỹ‖ | Ω_{ζ,b,I} = ω₀] ≤ C_cg (√((N + D_p)/(ζ b) + (p + 1)/ζ²) + √(N d / (ζ² b³) · C(ζ,3)))`,
and `H̃ᵀ Ỹ = 0` whenever `I = ∅` or `d = 0`. -/
def Lemma_5_4_IsolatedCrossTerm : Prop :=
  ∃ C_cg : ℝ, 0 < C_cg ∧
    (∀ (ζ b n : ℕ) (I : Finset (Fin n)) (ω : SketchSample ζ b n) (V : Matrix (Fin n) (Fin 0) ℝ),
      retainedCrossGram I V ω = 0) ∧
    (∀ (ζ b n d : ℕ) (ω : SketchSample ζ b n) (V : Matrix (Fin n) (Fin d) ℝ),
      retainedCrossGram ∅ V ω = 0) ∧
    ∀ (ζ b n d p : ℕ), 1 ≤ ζ → 2 * ζ ≤ b → 1 ≤ d → 1 ≤ p →
      Real.log (2 * (d : ℝ)) ≤ (p : ℝ) →
      ∀ (I : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ),
        1 ≤ I.card → IsIsometry V → (∀ i ∈ I, ∀ j : Fin d, V i j = 0) →
        ∀ ω₀ : SketchSample ζ b n,
          uniformMeanReal (SketchSample ζ b n)
            (fun ω => spectralNorm (retainedCrossGram I V (mergeHeadSample I ω₀ ω))) ≤
            C_cg * (Real.sqrt (((I.card : ℝ) + ((d : ℝ) + 2 * (p : ℝ) + 1)) / ((ζ * b : ℕ) : ℝ) +
                ((p : ℝ) + 1) / (ζ : ℝ) ^ 2) +
              Real.sqrt ((I.card : ℝ) * (d : ℝ) / ((ζ : ℝ) ^ 2 * (b : ℝ) ^ 3) *
                (Nat.choose ζ 3 : ℝ)))

/-- **Lemma 5.5 (High-moment bound for the full SparseStack Gram error, p. 28):**
There exists an absolute constant `C_mom > 0` such that for any fixed isometry `U ∈ ℝ^{n×D}`
(`D ≥ 1`), `b ≥ 2`, `ζ ≥ 1`, and `p ≥ 1`, with `G = Uᵀ Ω_{ζ,b} Ω_{ζ,b}ᵀ U` (`k = ζ b`),
`E[‖G - I_D‖^{2p}] ≤ D [C_mom (√((D + 2p + 1)/k) + (D + 2p + 1)/k + (2p + 1)/ζ)]^{2p}`. -/
def Lemma_5_5_FullSketchMoment : Prop :=
  ∃ C_mom : ℝ, 0 < C_mom ∧
    ∀ (ζ b n D p : ℕ), 1 ≤ ζ → 2 ≤ b → 1 ≤ D → 1 ≤ p →
      ∀ U : Matrix (Fin n) (Fin D) ℝ, IsIsometry U →
        uniformMeanReal (SketchSample ζ b n)
          (fun ω =>
            let A := (sparseStackOmega ω).transpose * U
            spectralNorm (A.transpose * A - 1) ^ (2 * p)) ≤
          (D : ℝ) * (C_mom * (Real.sqrt (((D : ℝ) + 2 * (p : ℝ) + 1) / ((ζ * b : ℕ) : ℝ)) +
            ((D : ℝ) + 2 * (p : ℝ) + 1) / ((ζ * b : ℕ) : ℝ) +
            (2 * (p : ℝ) + 1) / (ζ : ℝ))) ^ (2 * p)

/-- **Lemma 6.1 (Norm preservation for well-isolated coordinates in a single group, p. 30):**
For any `t₀ > 0`, `δ_rep ∈ (0, 1)`, and `H₀ > 0`, there exist `C₀, K₀ > 0` such that for all
`R ≥ 2`, `C₀ √log(e R) ≤ ζ₀ ≤ H₀ log(e R)`, `k₀ = ζ₀ b ≥ K₀ R`, `b ≥ 2 ζ₀`, `I₀ ⊆ [n]` with
`|I₀| ≤ R`, any fixed isometry `V₀ ∈ ℝ^{n×d₀}` (`d₀ ≤ 2 R`) supported off `I₀`, and any head
configuration `ω₀` of `I₀`, with probability at least `1 - δ_rep / 4` over the background `I₀ᶜ`,
simultaneously for all `h` supported on `I₀` and `f ∈ ℝ^{d₀}`:
`‖Ω_{ζ₀,b}ᵀ(h + V₀ f)‖² + t₀ ‖f‖² ≥ (11/12 - t₀) ‖h_{G₀}‖² - t₀ ‖h_{B₀}‖²`. -/
def Lemma_6_1_SingleGroup : Prop :=
  ∀ (t₀ δ_rep H₀ : ℝ), 0 < t₀ → 0 < δ_rep → δ_rep < 1 → 0 < H₀ →
    ∃ (C₀ K₀ : ℝ), 0 < C₀ ∧ 0 < K₀ ∧
      ∀ (n R ζ₀ b d₀ : ℕ), 2 ≤ R →
        C₀ * Real.sqrt (Real.log (Real.exp 1 * (R : ℝ))) ≤ (ζ₀ : ℝ) →
        (ζ₀ : ℝ) ≤ H₀ * Real.log (Real.exp 1 * (R : ℝ)) →
        K₀ * (R : ℝ) ≤ ((ζ₀ * b : ℕ) : ℝ) →
        2 * ζ₀ ≤ b →
        d₀ ≤ 2 * R →
        ∀ (I₀ : Finset (Fin n)) (V₀ : Matrix (Fin n) (Fin d₀) ℝ),
          I₀.card ≤ R → IsIsometry V₀ → (∀ i ∈ I₀, ∀ j : Fin d₀, V₀ i j = 0) →
          ∀ ω₀ : SketchSample ζ₀ b n,
            let G₀ := I₀.filter (fun i => (11 / 12 : ℝ) * (ζ₀ : ℝ) ≤ (isolatedBlockCount I₀ ω₀ i : ℝ))
            let B₀ := I₀ \ G₀
            (1 - δ_rep / 4) ≤ uniformProb (SketchSample ζ₀ b n)
              (fun ω => ∀ (h : Fin n → ℝ) (f : Fin d₀ → ℝ),
                (∀ i : Fin n, i ∉ I₀ → h i = 0) →
                (11 / 12 - t₀) * vecSqNorm (coordVec G₀ h) - t₀ * vecSqNorm (coordVec B₀ h) ≤
                  vecSqNorm ((sparseStackOmega (mergeHeadSample I₀ ω₀ ω)).transpose.mulVec
                    (h + V₀.mulVec f)) + t₀ * vecSqNorm f)

/-- **Lemma 6.2 (Two-group balls-into-bins isolation, p. 31, exact `c₁ = 1/1152`):**
Fix `δ_rep ∈ (0, 1)` and `c₁ = 1/1152`. There exists `C_iso > 0` such that for all `R ≥ 2`,
`b ≥ 1`, `ζ₀ ≥ C_iso √log(e R)`, and `I ⊆ [n]` with `N = |I| ≤ min{R, b / 16}`:
(i) over Group 1 (`ω₁`), `|B| ≤ N exp(- c₁ ζ₀)` with probability at least `1 - δ_rep / 4`;
(ii) for every realization `ω₁` with `|B| ≤ N exp(- c₁ ζ₀)`, over Group 2 (`ω₂`), every `i ∈ B`
has `aᵢ^{(2)} ≥ (11/12) ζ₀` with probability at least `1 - δ_rep / 4`. -/
def Lemma_6_2_TwoGroupIsolation : Prop :=
  ∀ δ_rep : ℝ, 0 < δ_rep → δ_rep < 1 →
    let c₁ : ℝ := 1 / 1152
    ∃ C_iso : ℝ, 0 < C_iso ∧
      ∀ (n R ζ₀ b : ℕ), 2 ≤ R → 1 ≤ b →
        C_iso * Real.sqrt (Real.log (Real.exp 1 * (R : ℝ))) ≤ (ζ₀ : ℝ) →
        ∀ I : Finset (Fin n), I.card ≤ R → 16 * I.card ≤ b →
          let B_of : SketchSample ζ₀ b n → Finset (Fin n) :=
            fun ω₁ => I \ I.filter
              (fun i => (11 / 12 : ℝ) * (ζ₀ : ℝ) ≤ (isolatedBlockCount I ω₁ i : ℝ))
          ((1 - δ_rep / 4) ≤ uniformProb (SketchSample ζ₀ b n)
            (fun ω₁ => ((B_of ω₁).card : ℝ) ≤ (I.card : ℝ) * Real.exp (-c₁ * (ζ₀ : ℝ)))) ∧
          (∀ ω₁ : SketchSample ζ₀ b n,
            ((B_of ω₁).card : ℝ) ≤ (I.card : ℝ) * Real.exp (-c₁ * (ζ₀ : ℝ)) →
            (1 - δ_rep / 4) ≤ uniformProb (SketchSample ζ₀ b n)
              (fun ω₂ => ∀ i ∈ B_of ω₁,
                (11 / 12 : ℝ) * (ζ₀ : ℝ) ≤ (isolatedBlockCount (B_of ω₁) ω₂ i : ℝ)))

/-- **Lemma 6.3 (Two-group lower bound for heavy coordinates, p. 32):**
For any `t₀ ∈ (0, 1/4)` and `δ_rep ∈ (0, 1)`, there exist `C⋆, K⋆ > 0` and `ρ₀ ∈ [1/3, 1/2]`
with `β = ρ₀ (11/12 - 2 t₀) > 0` such that for all `R ≥ 2`, `ζ ≥ C⋆ √log(e R)`, `k = ζ b ≥ K⋆ R`,
`I ⊆ [n]` with `|I| ≤ min{R, b / 16}`, and any fixed isometry `V ∈ ℝ^{n×d}` (`d ≤ R`) supported
off `I`, with probability at least `1 - δ_rep`, simultaneously for all `h` supported on `I` and
`f ∈ ℝ^d`, `‖Ω_{ζ,b}ᵀ(h + V f)‖² + t₀ ‖f‖² ≥ β ‖h‖²`. -/
def Lemma_6_3_TwoGroupHeavy : Prop :=
  ∀ (t₀ δ_rep : ℝ), 0 < t₀ → t₀ < 1 / 4 → 0 < δ_rep → δ_rep < 1 →
    ∃ (C_star K_star ρ₀ : ℝ), 0 < C_star ∧ 0 < K_star ∧ 1 / 3 ≤ ρ₀ ∧ ρ₀ ≤ 1 / 2 ∧
      let β := ρ₀ * (11 / 12 - 2 * t₀)
      0 < β ∧
      ∀ (n R ζ b d : ℕ), 2 ≤ R →
        C_star * Real.sqrt (Real.log (Real.exp 1 * (R : ℝ))) ≤ (ζ : ℝ) →
        K_star * (R : ℝ) ≤ ((ζ * b : ℕ) : ℝ) →
        d ≤ R →
        ∀ (I : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ),
          I.card ≤ R → 16 * I.card ≤ b → IsIsometry V → (∀ i ∈ I, ∀ j : Fin d, V i j = 0) →
          (1 - δ_rep) ≤ uniformProb (SketchSample ζ b n)
            (fun ω => ∀ (h : Fin n → ℝ) (f : Fin d → ℝ),
              (∀ i : Fin n, i ∉ I → h i = 0) →
              β * vecSqNorm h ≤
                vecSqNorm ((sparseStackOmega ω).transpose.mulVec (h + V.mulVec f)) +
                  t₀ * vecSqNorm f)

/-! ## 6. Sections 8–10 Lower-Bound Pipeline Definitions & Statements -/

/-- Heavy rows `I_heavy = {i ∈ [n] : ‖sᵢ‖₂² > M}` (Section 8.1, p. 37). -/
noncomputable def heavyRows {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (M : ℝ) :
    Finset (Fin n) :=
  (Set.toFinite {i : Fin n | M < vecSqNorm (S i)}).toFinset

/-- Small-norm rows `I_small = {i ∈ [n] : ‖sᵢ‖₂² < α}` (Section 8.1, p. 37). -/
noncomputable def smallRows {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (α : ℝ) :
    Finset (Fin n) :=
  (Set.toFinite {i : Fin n | vecSqNorm (S i) < α}).toFinset

/-- One-sparse rows `I_one = {i ∈ [n] : |supp(sᵢ)| = 1}` (Section 8.1, p. 37). -/
noncomputable def oneSparseRows {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) :
    Finset (Fin n) :=
  (Set.toFinite {i : Fin n | (rowSupport S i).card = 1}).toFinset

/-- Clean rows `V_clean = [n] \ (I_heavy ∪ I_small ∪ I_one)` (Eq. (38), p. 38). -/
noncomputable def cleanRows {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (α M : ℝ) :
    Finset (Fin n) :=
  Finset.univ \ (heavyRows S M ∪ smallRows S α ∪ oneSparseRows S)

/-- Colliding row pairs `(u, v)` (`u < v`) inside a subset `V₀ ⊆ [n]` sharing `≥ 2` columns. -/
noncomputable def subCollidingPairs {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (V₀ : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (Set.toFinite {uv : Fin n × Fin n |
    uv.1 ∈ V₀ ∧ uv.2 ∈ V₀ ∧ uv.1 < uv.2 ∧
      2 ≤ (rowSupport S uv.1 ∩ rowSupport S uv.2).card}).toFinset

/-- `C₄`-freeness of the induced row-column bipartite graph on `V_G0 ⊆ [n]`: no two distinct rows
in `V_G0` share two or more non-zero columns. -/
def IsC4FreeRows {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (V_G0 : Finset (Fin n)) : Prop :=
  ∀ u ∈ V_G0, ∀ v ∈ V_G0, u ≠ v → (rowSupport S u ∩ rowSupport S v).card ≤ 1

/-- Pruned `C₄`-free row set `V(G₀) ⊆ V₀ ∩ V_clean` obtained by discarding `V₀ \ V_clean` and
removing the larger index `max{u, v}` of any colliding pair in `V₀ ∩ V_clean` (Section 8.2, p. 38). -/
noncomputable def prunedRows {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (α M : ℝ)
    (V₀ : Finset (Fin n)) : Finset (Fin n) :=
  (Set.toFinite {v : Fin n |
    v ∈ V₀ ∩ cleanRows S α M ∧
      ∀ u ∈ V₀ ∩ cleanRows S α M, u < v → (rowSupport S u ∩ rowSupport S v).card ≤ 1}).toFinset

/-- Relative entry weight `w_{i,j} = S_{i,j}² / ‖sᵢ‖₂²` (Section 9, p. 39). -/
noncomputable def relWeight {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (i : Fin n) (j : Fin k) : ℝ :=
  (S i j) ^ 2 / vecSqNorm (S i)

/-- Single-tree star cancellation vector `x ∈ ℝ^n` (Eq. (39), Lemma 9.1, p. 40):
`x_{i*} = 1`, `x_ℓ = - S_{i*, j} / (q S_{ℓ, j})` for `j ∈ supp(s_{i*})` and `ℓ ∈ L j`, and `0`
elsewhere. -/
noncomputable def treeCancelVec {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (iStar : Fin n)
    (q : ℕ) (L : Fin k → Finset (Fin n)) : Fin n → ℝ :=
  fun m =>
    if m = iStar then 1
    else ∑ j ∈ rowSupport S iStar,
      if m ∈ L j then -(S iStar j) / ((q : ℝ) * S m j) else 0

/-- Virtual-column splitting and top-`D` candidate-set structure on `G₀` (Section 9.3, pp. 42–43):
each column `j ∈ [k]` has its incident rows in `V_G0` partitioned into virtual columns of degree at
most `Δ`, producing `k' ≤ 2 k` virtual columns `V_virt : Fin k' → Finset (Fin n)` with underlying
column map `colOf : Fin k' → Fin k` and top-`D` relative-weight candidate sets `F j' ⊆ V_virt j'`. -/
def IsVirtualColumnSplitting {n k k' : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (V_G0 : Finset (Fin n)) (Δ D : ℕ) (colOf : Fin k' → Fin k)
    (V_virt F : Fin k' → Finset (Fin n)) : Prop :=
  (∀ j' : Fin k', V_virt j' ⊆ V_G0) ∧
    (∀ j' : Fin k', ∀ i ∈ V_virt j', colOf j' ∈ rowSupport S i) ∧
    (∀ i ∈ V_G0, ∀ j ∈ rowSupport S i, ∃! j' : Fin k', colOf j' = j ∧ i ∈ V_virt j') ∧
    (∀ j' : Fin k', (V_virt j').card ≤ Δ) ∧
    (∀ j' : Fin k', F j' ⊆ V_virt j' ∧ (F j').card = min D (V_virt j').card ∧
      ∀ i ∈ V_virt j' \ F j', ∀ ℓ ∈ F j',
        relWeight S i (colOf j') ≤ relWeight S ℓ (colOf j'))

/-- **Lemma 8.1 (Heavy-row count bound, p. 37):**
With `M = 160`, in any matrix `S ∈ ℝ^{n×k}` satisfying `‖S‖_F² ≤ 10 n`, `|I_heavy| ≤ n / 16`. -/
def Lemma_8_1_HeavyRowCount : Prop :=
  ∀ (n k : ℕ) (S : Matrix (Fin n) (Fin k) ℝ),
    frobSq S ≤ 10 * (n : ℝ) → ((heavyRows S 160).card : ℝ) ≤ (n : ℝ) / 16

/-- **Lemma 8.2 (Elimination of small-norm or one-sparse rows, p. 37):**
There exists a universal constant `C₀ > 0` such that for all `K ≥ 1`, `α > 0`, `r ≥ C₀ K`,
`n ≥ 64 K r`, and `k ≤ K r`, in any `S ∈ ℝ^{n×k}` having `|I_small| ≥ n / 16` or
`|I_one| ≥ n / 16`, a uniformly random `r`-subset `R ⊆ [n]` satisfies
`Pr_R(σ_min(S_Rᵀ)² < α) ≥ 9 / 10`. -/
def Lemma_8_2_SmallOrOneSparseElim : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (K α : ℝ) (n r k : ℕ) (S : Matrix (Fin n) (Fin k) ℝ),
      1 ≤ K → 0 < α → C₀ * K ≤ (r : ℝ) → 64 * K * (r : ℝ) ≤ (n : ℝ) →
      (k : ℝ) ≤ K * (r : ℝ) → r ≤ n →
      ((n : ℝ) / 16 ≤ (smallRows S α).card ∨ (n : ℝ) / 16 ≤ (oneSparseRows S).card) →
      (9 / 10 : ℝ) ≤ uniformSubsetProb n r
        (fun R => ∀ hR : R.card = r, ¬ MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α)

/-- **Lemma 8.3 (`C₄`-free subsampled subgraph `G₀`, p. 38):**
There exists a constant `C_samp₀ > 0` such that for every `C_samp ≥ C_samp₀`, `α ∈ (0, 1]`,
`1 ≤ r ≤ k`, `ζ ≥ 1`, and every row-`ζ`-sparse `S ∈ ℝ^{n×k}` satisfying Definition 1.2 with
`η ≤ (512 C_samp ζ⁶ / α)⁻¹` and `|V_clean| ≥ 13 n / 16`, if `n₀ = ⌈C_samp r ζ⁶ / α⌉ ≤ n`, then
uniformly subsampling `V₀ ∈ ([n] choose n₀)` yields with probability at least `7 / 8`:
`|V₀ \ V_clean| ≤ n₀ / 4`, `|subCollidingPairs S V₀| ≤ n₀ / 16`, `|V(G₀)| ≥ 5 n₀ / 8`, `G₀` is
`C₄`-free, and every `i ∈ V(G₀)` has `α ≤ ‖sᵢ‖₂² ≤ 160` and `2 ≤ |supp(sᵢ)| ≤ ζ`. -/
def Lemma_8_3_C4FreeSubgraph : Prop :=
  ∃ C_samp₀ : ℝ, 0 < C_samp₀ ∧
    ∀ (C_samp α : ℝ) (n k r ζ : ℕ) (S : Matrix (Fin n) (Fin k) ℝ),
      C_samp₀ ≤ C_samp → 0 < α → α ≤ 1 → 1 ≤ r → r ≤ k → 1 ≤ ζ →
      (∀ i : Fin n, (rowSupport S i).card ≤ ζ) →
      SatisfiesOverlapCond S (((512 * C_samp / α) * (ζ : ℝ) ^ 6)⁻¹) →
      (13 / 16 : ℝ) * (n : ℝ) ≤ ((cleanRows S α 160).card : ℝ) →
      ∀ n₀ : ℕ, n₀ = Nat.ceil (C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α) → n₀ ≤ n →
        (7 / 8 : ℝ) ≤ uniformSubsetProb n n₀
          (fun V₀ =>
            let V_G0 := prunedRows S α 160 V₀
            (((V₀ \ cleanRows S α 160).card : ℝ) ≤ (n₀ : ℝ) / 4) ∧
              (((subCollidingPairs S V₀).card : ℝ) ≤ (n₀ : ℝ) / 16) ∧
              ((5 / 8 : ℝ) * (n₀ : ℝ) ≤ (V_G0.card : ℝ)) ∧
              IsC4FreeRows S V_G0 ∧
              ∀ i ∈ V_G0, α ≤ vecSqNorm (S i) ∧ vecSqNorm (S i) ≤ 160 ∧
                2 ≤ (rowSupport S i).card ∧ (rowSupport S i).card ≤ ζ)

/-- **Lemma 9.1 (Single-tree inner cancellation and outer energy bound, p. 40):**
In a `C₄`-free row set `V_G0`, let `i* ∈ V_G0` have `d = |supp(s_{i*})| ≤ ζ`, and for each branch
column `j ∈ supp(s_{i*})` let `L j ⊆ V_G0 \ {i*}` be `q ≥ 1` leaf rows with `j ∈ supp(s_ℓ)`,
`w_{ℓ,j} ≥ w_{i*,j}`, and pairwise disjoint outer supports `supp(s_ℓ) \ {j}` across all leaves.
Then `x = treeCancelVec S i* q L` cancels every branch column `(Sᵀ x)_j = 0` (`j ∈ supp(s_{i*})`)
and satisfies `∑_{c ∉ supp(s_{i*})} |(Sᵀ x)_c|² ≤ d ‖s_{i*}‖₂² / q`. -/
def Lemma_9_1_TreeCancellation : Prop :=
  ∀ (n k ζ q : ℕ) (S : Matrix (Fin n) (Fin k) ℝ) (V_G0 : Finset (Fin n))
    (iStar : Fin n) (L : Fin k → Finset (Fin n)),
    1 ≤ q →
    IsC4FreeRows S V_G0 →
    iStar ∈ V_G0 →
    (rowSupport S iStar).card ≤ ζ →
    (∀ j ∈ rowSupport S iStar, L j ⊆ V_G0 \ {iStar} ∧ (L j).card = q ∧
      ∀ ℓ ∈ L j, j ∈ rowSupport S ℓ ∧ relWeight S iStar j ≤ relWeight S ℓ j) →
    (∀ j₁ ∈ rowSupport S iStar, ∀ ℓ₁ ∈ L j₁, ∀ j₂ ∈ rowSupport S iStar, ∀ ℓ₂ ∈ L j₂,
      (j₁, ℓ₁) ≠ (j₂, ℓ₂) →
        Disjoint (rowSupport S ℓ₁ \ {j₁}) (rowSupport S ℓ₂ \ {j₂})) →
    let x := treeCancelVec S iStar q L
    (∀ j ∈ rowSupport S iStar, (S.transpose.mulVec x) j = 0) ∧
      (∑ c ∈ (rowSupport S iStar)ᶜ, ((S.transpose.mulVec x) c) ^ 2) ≤
        ((rowSupport S iStar).card : ℝ) * vecSqNorm (S iStar) / (q : ℝ)

/-- **Lemma 9.2 (Greedy outer-disjoint leaf selection for a single tree, p. 41):**
In a `C₄`-free row set `V_G0` where every row has support size `≤ ζ` (`ζ ≥ 1`), if `i* ∈ V_G0` and
for each branch `j ∈ supp(s_{i*})` we have `F j ⊆ V_G0 \ {i*}` with `j ∈ supp(s_ℓ)` (`ℓ ∈ F j`)
and `|F j| ≥ q + q (ζ - 1)²`, then there exist `L j ⊆ F j` of size `q` whose outer supports
`supp(s_ℓ) \ {j}` are pairwise disjoint across all branches and leaves. -/
def Lemma_9_2_SingleTreeDisjointLeaves : Prop :=
  ∀ (n k ζ q : ℕ) (S : Matrix (Fin n) (Fin k) ℝ) (V_G0 : Finset (Fin n))
    (iStar : Fin n) (F : Fin k → Finset (Fin n)),
    1 ≤ ζ →
    IsC4FreeRows S V_G0 →
    (∀ i ∈ V_G0, (rowSupport S i).card ≤ ζ) →
    iStar ∈ V_G0 →
    (∀ j ∈ rowSupport S iStar, F j ⊆ V_G0 \ {iStar} ∧
      (∀ ℓ ∈ F j, j ∈ rowSupport S ℓ) ∧
      q + q * (ζ - 1) ^ 2 ≤ (F j).card) →
    ∃ L : Fin k → Finset (Fin n),
      (∀ j ∈ rowSupport S iStar, L j ⊆ F j ∧ (L j).card = q) ∧
        ∀ j₁ ∈ rowSupport S iStar, ∀ ℓ₁ ∈ L j₁, ∀ j₂ ∈ rowSupport S iStar, ∀ ℓ₂ ∈ L j₂,
          (j₁, ℓ₁) ≠ (j₂, ℓ₂) →
            Disjoint (rowSupport S ℓ₁ \ {j₁}) (rowSupport S ℓ₂ \ {j₂})

/-- **Lemma 9.3 (Turán / Caro–Wei independent-set lower bound, p. 42):**
Every finite simple graph `H` on `m ≥ 1` vertices with edge count `|E_H|` and average degree
`d_avg = 2 |E_H| / m` contains an independent set `I` of size `|I| ≥ m / (1 + d_avg)`. -/
def Lemma_9_3_TuranCaroWei : Prop :=
  ∀ (m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ m →
    let edgeCount : ℕ := ((Set.toFinite H.edgeSet).toFinset).card
    let d_avg : ℝ := 2 * (edgeCount : ℝ) / (m : ℝ)
    ∃ I : Finset (Fin m),
      (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ H.Adj u v) ∧
        (m : ℝ) / (1 + d_avg) ≤ (I.card : ℝ)

/-- **Lemma 9.4 (Virtual column splitting and Turán extraction of center rows, p. 42):**
There exist constants `C_samp₁ > 0` and `c_T > 0` such that for `K ≥ 1`, `α ∈ (0, 1]`,
`C_samp ≥ C_samp₁ K`, `2 ≤ r ≤ k`, `k ≤ K r`, `ζ ≥ 2`, `n₀ = ⌈C_samp r ζ⁶ / α⌉`, `D = ζ L` with
`L = q + q (ζ - 1)²` and `q = ⌈640 ζ / α⌉`, and `V_G0` with `(5/8) n₀ ≤ |V_G0| ≤ n₀` and row
sparsity `≤ ζ`: there exist a virtual-column splitting `(k' ≤ 2 k, colOf, V_virt, F)` with degree
cap `Δ = ⌈ζ n₀ / k⌉` and a subset `I_center ⊆ J_elig = V_G0 \ ⋃_{j'} F j'` of size
`|I_center| ≥ c_T r / ζ⁵` whose virtual-column supports are pairwise disjoint. -/
def Lemma_9_4_TuranCenterRows : Prop :=
  ∃ (C_samp₁ c_T : ℝ), 0 < C_samp₁ ∧ 0 < c_T ∧
    ∀ (K C_samp α : ℝ) (n k r ζ n₀ : ℕ) (S : Matrix (Fin n) (Fin k) ℝ) (V_G0 : Finset (Fin n)),
      1 ≤ K → C_samp₁ * K ≤ C_samp → 0 < α → α ≤ 1 →
      2 ≤ r → r ≤ k → (k : ℝ) ≤ K * (r : ℝ) → 2 ≤ ζ →
      n₀ = Nat.ceil (C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α) →
      (5 / 8 : ℝ) * (n₀ : ℝ) ≤ (V_G0.card : ℝ) →
      V_G0.card ≤ n₀ →
      (∀ i ∈ V_G0, (rowSupport S i).card ≤ ζ) →
      let Δ : ℕ := Nat.ceil ((ζ : ℝ) * (n₀ : ℝ) / (k : ℝ))
      let q : ℕ := Nat.ceil (640 * (ζ : ℝ) / α)
      let L : ℕ := q + q * (ζ - 1) ^ 2
      let D : ℕ := ζ * L
      ∃ (k' : ℕ) (colOf : Fin k' → Fin k) (V_virt F : Fin k' → Finset (Fin n))
        (I_center : Finset (Fin n)),
        k' ≤ 2 * k ∧
          IsVirtualColumnSplitting S V_G0 Δ D colOf V_virt F ∧
          I_center ⊆ V_G0 \ Finset.univ.biUnion F ∧
          c_T * (r : ℝ) / (ζ : ℝ) ^ 5 ≤ (I_center.card : ℝ) ∧
          ∀ u ∈ I_center, ∀ v ∈ I_center, u ≠ v →
            ∀ j' : Fin k', ¬ (u ∈ V_virt j' ∧ v ∈ V_virt j')

/-- **Lemma 9.5 (Hall's Marriage Theorem for finite bipartite graphs, p. 43):**
In a finite bipartite graph `R ⊆ V_L × V_R`, there exists a matching saturating `V_L` (an injective
choice `f : V_L → V_R` with `R u (f u)` for all `u`) if and only if `|N(A)| ≥ |A|` for every
`A ⊆ V_L`. -/
def Lemma_9_5_HallMarriage : Prop :=
  ∀ (m n : ℕ) (R : Fin m → Fin n → Prop),
    (∃ f : Fin m → Fin n, Function.Injective f ∧ ∀ u : Fin m, R u (f u)) ↔
      ∀ A : Finset (Fin m),
        A.card ≤ ((Set.toFinite {v : Fin n | ∃ u ∈ A, R u v}).toFinset).card

/-- **Lemma 9.6 (Simultaneous allocation of disjoint leaf reservoirs, p. 43):**
If each active branch virtual column `j' ∈ J_branch` has candidate set `F j'` of size `|F j'| ≥ D`
with `D ≥ ζ L` (`ζ ≥ 1`), and each row `ℓ ∈ [n]` belongs to `F j'` for at most `ζ` virtual columns
`j' ∈ J_branch`, then there exist pairwise disjoint subsets `R_res j' ⊆ F j'` of size `L` for all
`j' ∈ J_branch`. -/
def Lemma_9_6_DisjointLeafReservoirs : Prop :=
  ∀ (n k' ζ L D : ℕ) (J_branch : Finset (Fin k')) (F : Fin k' → Finset (Fin n)),
    1 ≤ ζ → ζ * L ≤ D →
    (∀ j' ∈ J_branch, D ≤ (F j').card) →
    (∀ ℓ : Fin n,
      ((Set.toFinite {j' : Fin k' | j' ∈ J_branch ∧ ℓ ∈ F j'}).toFinset).card ≤ ζ) →
    ∃ R_res : Fin k' → Finset (Fin n),
      (∀ j' ∈ J_branch, R_res j' ⊆ F j' ∧ (R_res j').card = L) ∧
        ∀ j₁' ∈ J_branch, ∀ j₂' ∈ J_branch, j₁' ≠ j₂' → Disjoint (R_res j₁') (R_res j₂')

/-- **Theorem 9.7 (Existence of a vertex-disjoint witness forest in `G₀`, p. 44):**
There exist constants `C_samp₂ > 0` and `c_T > 0` such that under the `C₄`-free clean subgraph
conditions of Lemma 8.3 (`(5/8) n₀ ≤ |V_G0| ≤ n₀` with `C_samp ≥ C_samp₂ K²` and
`q = ⌈640 ζ / α⌉`), `V_G0` contains `T ≥ 1` (`T ≥ c_T r / ζ⁵`) pairwise disjoint vertex sets
`V_tree s ⊆ V_G0` of exact size `1 + ζ q` together with witness vectors `x_tree s ∈ ℝ^n` supported
on `V_tree s` satisfying `‖x_tree s‖₂² ≥ 1` and `‖Sᵀ x_tree s‖₂² ≤ α / 4`. -/
def Theorem_9_7_WitnessForest : Prop :=
  ∃ (C_samp₂ c_T : ℝ), 0 < C_samp₂ ∧ 0 < c_T ∧
    ∀ (K C_samp α : ℝ) (n k r ζ n₀ : ℕ) (S : Matrix (Fin n) (Fin k) ℝ) (V_G0 : Finset (Fin n)),
      1 ≤ K → C_samp₂ * K ^ 2 ≤ C_samp → 0 < α → α ≤ 1 →
      2 ≤ r → r ≤ k → (k : ℝ) ≤ K * (r : ℝ) → 2 ≤ ζ →
      n₀ = Nat.ceil (C_samp * (r : ℝ) * (ζ : ℝ) ^ 6 / α) →
      (5 / 8 : ℝ) * (n₀ : ℝ) ≤ (V_G0.card : ℝ) →
      V_G0.card ≤ n₀ →
      IsC4FreeRows S V_G0 →
      (∀ i ∈ V_G0, α ≤ vecSqNorm (S i) ∧ vecSqNorm (S i) ≤ 160 ∧
        2 ≤ (rowSupport S i).card ∧ (rowSupport S i).card ≤ ζ) →
      let q : ℕ := Nat.ceil (640 * (ζ : ℝ) / α)
      ∃ (T : ℕ) (V_tree : Fin T → Finset (Fin n)) (x_tree : Fin T → Fin n → ℝ),
        1 ≤ T ∧
          c_T * (r : ℝ) / (ζ : ℝ) ^ 5 ≤ (T : ℝ) ∧
          (∀ s : Fin T, V_tree s ⊆ V_G0 ∧ (V_tree s).card = 1 + ζ * q) ∧
          (∀ s u : Fin T, s ≠ u → Disjoint (V_tree s) (V_tree u)) ∧
          (∀ s : Fin T, (∀ i : Fin n, i ∉ V_tree s → x_tree s i = 0) ∧
            1 ≤ vecSqNorm (x_tree s) ∧
            vecSqNorm (S.transpose.mulVec (x_tree s)) ≤ α / 4)

/-- **Lemma 10.1 (Coordinate-subspace minimax reduction, p. 45):**
Let `1 ≤ r ≤ n`, `α ∈ (0, 1)`, and `η ≥ 0`. Suppose every fixed matrix `S ∈ ℝ^{n×k}` with row
sparsity `ζ`, `‖S‖_F² ≤ 10 n`, and `SatisfiesOverlapCond S η` satisfies
`Pr_{R ∼ Unif([n] choose r)}(σ_min(S_Rᵀ)² ≥ α) ≤ 1/4`. Then no isotropic random matrix
`M : Ω_prob → ℝ^{n×k}` with row sparsity `ζ` and `SatisfiesOverlapWhp P M η (9/10)` can satisfy
`IsOSIWithProb P M r α p_osi` for any `p_osi > 9/20` (in particular for `1/2`, `9/10`, or `19/20`). -/
def Lemma_10_1_CoordinateSubspaceReduction : Prop :=
  ∀ (n r k ζ : ℕ) (α η p_osi : ℝ),
    1 ≤ r → r ≤ n → 0 < α → α < 1 → 0 ≤ η → 9 / 20 < p_osi →
    (∀ S : Matrix (Fin n) (Fin k) ℝ,
      (∀ i : Fin n, (rowSupport S i).card ≤ ζ) →
      frobSq S ≤ 10 * (n : ℝ) →
      SatisfiesOverlapCond S η →
      uniformSubsetProb n r
        (fun R => ∀ hR : R.card = r, MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α) ≤
        1 / 4) →
    ∀ (Ω_prob : Type) [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob),
      MeasureTheory.IsProbabilityMeasure P →
      ∀ M : Ω_prob → Matrix (Fin n) (Fin k) ℝ,
        IsRandomMatrix M →
        IsIsotropic P M →
        IsRowSparse P M ζ →
        SatisfiesOverlapWhp P M η (9 / 10) →
        ¬ IsOSIWithProb P M r α p_osi

/-- **Theorem 10.2 (Finite-scale coordinate-capture theorem & full OSI lower bound, p. 46):**
Combines the deterministic fixed-matrix random-coordinate capture bound
`Pr_{R ∼ Unif([n] choose r)}(σ_min(S_Rᵀ)² ≥ α) ≤ 1/4` whenever `ζ ≤ c √(log r / log log r)` with
Lemma 10.1 to deduce the row-sparsity lower bound `ζ ≥ c √(log r / log log r)`. -/
def Theorem_10_2_FiniteScale : Prop :=
  ∀ (K α : ℝ), 1 ≤ K → 0 < α → α < 1 →
    ∃ (c C_H C_n : ℝ) (r₀ : ℕ), 0 < c ∧ 0 < C_H ∧ 0 < C_n ∧ 3 ≤ r₀ ∧
      (∀ (n r k ζ : ℕ) (S : Matrix (Fin n) (Fin k) ℝ),
        r₀ ≤ r → r ≤ n →
        C_n * (r : ℝ) * (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 ≤ (n : ℝ) →
        r ≤ k → (k : ℝ) ≤ K * (r : ℝ) →
        (ζ : ℝ) ≤ c * Real.sqrt (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) →
        (∀ i : Fin n, (rowSupport S i).card ≤ ζ) →
        frobSq S ≤ 10 * (n : ℝ) →
        SatisfiesOverlapCond S ((C_H * (ζ : ℝ) ^ 6)⁻¹) →
        uniformSubsetProb n r
          (fun R => ∀ hR : R.card = r, MinEigenvalueAtLeast (S.transpose * coordFrame R hR) α) ≤
          1 / 4) ∧
      (∀ (n r k ζ : ℕ), r₀ ≤ r → r ≤ n →
        C_n * (r : ℝ) * (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ^ 3 ≤ (n : ℝ) →
        (k : ℝ) ≤ K * (r : ℝ) →
        ∀ (Ω_prob : Type) [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob),
          MeasureTheory.IsProbabilityMeasure P →
          ∀ M : Ω_prob → Matrix (Fin n) (Fin k) ℝ,
            IsRandomMatrix M →
            IsIsotropic P M →
            IsRowSparse P M ζ →
            SatisfiesOverlapWhp P M ((C_H * (ζ : ℝ) ^ 6)⁻¹) (9 / 10) →
            IsOSI P M r α →
            c * Real.sqrt (Real.log (r : ℝ) / Real.log (Real.log (r : ℝ))) ≤ (ζ : ℝ))

/-- Conjunction of all 26 numbered paper statements plus all 9 main-result / tightness variants
across Sections 1–10. -/
def AllPaperTheorems : Prop :=
  Theorem_1_1_GeneralParams ∧
    Theorem_1_1_PaperRange ∧
    Theorem_1_1_Schedule ∧
    Proposition_SparseStack_Overlap ∧
    Theorem_1_3_LowerBound_HalfProb ∧
    Theorem_1_3_LowerBound ∧
    Theorem_1_3_QuadraticN ∧
    Theorem_1_3_NecessityOfAmbientBound ∧
    Theorem_Optimal_SparseStack_Tightness ∧
    Theorem_2_1_FlatPreservation ∧
    Theorem_2_2_CommonSupport ∧
    Theorem_2_3_HeavyPreservation ∧
    Lemma_3_2_WeightedBernoulli ∧
    Lemma_3_3_PointwiseFlat ∧
    Lemma_3_4_LatticeRounding ∧
    Lemma_4_1_GaussianTruncation ∧
    Lemma_4_2_MinimaxSelection ∧
    Lemma_5_3_IidOpNorm ∧
    Lemma_5_4_IsolatedCrossTerm ∧
    Lemma_5_5_FullSketchMoment ∧
    Lemma_6_1_SingleGroup ∧
    Lemma_6_2_TwoGroupIsolation ∧
    Lemma_6_3_TwoGroupHeavy ∧
    Lemma_8_1_HeavyRowCount ∧
    Lemma_8_2_SmallOrOneSparseElim ∧
    Lemma_8_3_C4FreeSubgraph ∧
    Lemma_9_1_TreeCancellation ∧
    Lemma_9_2_SingleTreeDisjointLeaves ∧
    Lemma_9_3_TuranCaroWei ∧
    Lemma_9_4_TuranCenterRows ∧
    Lemma_9_5_HallMarriage ∧
    Lemma_9_6_DisjointLeafReservoirs ∧
    Theorem_9_7_WitnessForest ∧
    Lemma_10_1_CoordinateSubspaceReduction ∧
    Theorem_10_2_FiniteScale

/-! ## 7. Non-vacuity and sanity checks (`0 sorry`) -/

/-- Sanity check 1: `constAlpha ∈ (10⁻⁴, 1)`. -/
example : (1 / 10000 : ℝ) < constAlpha ∧ constAlpha < 1 := by
  unfold constAlpha
  norm_num

/-- Sanity check 2: the identity matrix `I₂` is an isometry. -/
example : IsIsometry (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  simp [IsIsometry]

/-- Sanity check 3: the `3 × 3` identity matrix satisfies `SatisfiesOverlapCond` with `η = 0`. -/
example : SatisfiesOverlapCond (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 := by
  unfold SatisfiesOverlapCond overlapPairCount
  have hempty : overlapPairs (1 : Matrix (Fin 3) (Fin 3) ℝ) = ∅ := by
    ext ⟨u, v⟩
    simp only [overlapPairs, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.notMem_empty,
      iff_false, not_and]
    intro huv hcard
    have hsub : rowSupport (1 : Matrix (Fin 3) (Fin 3) ℝ) u ∩
        rowSupport (1 : Matrix (Fin 3) (Fin 3) ℝ) v = ∅ := by
      ext j
      simp only [Finset.mem_inter, rowSupport, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
        Matrix.one_apply, Finset.notMem_empty, iff_false, not_and]
      intro h1 h2
      have hju : u = j := by
        by_contra hne
        exact h1 (if_neg hne)
      have hjv : v = j := by
        by_contra hne
        exact h2 (if_neg hne)
      exact huv.ne (hju.trans hjv.symm)
    rw [hsub] at hcard
    simp at hcard
  rw [hempty]
  simp

/-- Sanity check 4 (non-vacuity of Definition 1.2): the `2 × 2` all-ones matrix fails
`SatisfiesOverlapCond` at `η = 0`. -/
example : ¬ SatisfiesOverlapCond (Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ)) 0 := by
  unfold SatisfiesOverlapCond overlapPairCount
  have hmem : ((0 : Fin 2), (1 : Fin 2)) ∈
      overlapPairs (Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ)) := by
    simp only [overlapPairs, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    refine ⟨by decide, ?_⟩
    have hsupp : ∀ i : Fin 2,
        rowSupport (Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ)) i = Finset.univ := by
      intro i
      ext j
      simp [rowSupport]
    rw [hsupp, hsupp]
    decide
  have hpos : 1 ≤ (overlapPairs (Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ))).card :=
    Finset.one_le_card.mpr ⟨_, hmem⟩
  intro hle
  have h0 : ((overlapPairs (Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ))).card : ℝ) ≤ 0 := by
    simpa using hle
  have h1 : (1 : ℝ) ≤
      ((overlapPairs (Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ))).card : ℝ) := by
    exact_mod_cast hpos
  linarith

/-- Sanity check 5 (non-vacuity of `QuadraticLowerBound`): `I₂` satisfies `QuadraticLowerBound`
with `α = 1`, while `0` fails it at `α = 1/2`. -/
example :
    QuadraticLowerBound (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 ∧
      ¬ QuadraticLowerBound (0 : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) := by
  refine ⟨fun x => ?_, fun h => ?_⟩
  · simp [vecSqNorm]
  · have hx := h (fun _ => 1)
    simp [vecSqNorm] at hx
    linarith

end Spec
end Osi
