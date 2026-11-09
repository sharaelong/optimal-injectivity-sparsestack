import Mathlib

/-!
# Specification: *Optimal Injectivity of the SparseStack* — Upper Bound (Sections 1–7)

This file is the formal specification (`OsiUb/Spec.lean`) for the complete **Upper-Bound (UB)**
portion (Sections 1–7, pp. 1–40) of Kijun's revised manuscript
*"Optimal Injectivity of the SparseStack"* (`source/constant_injectivity_sparsestack-2.pdf`,
SHA-256 `0fcf41b556c345609b17144961b536898f3248b5cc13f150d923b442672bef78`).

It imports **only `Mathlib`** and contains plain, textbook mathematical definitions together with
`Prop`-valued statements of every UB definition, theorem, proposition, lemma, claim, and fact
across Sections 1–7:

* **Section 1.2 (Main UB Results & Overlap Property, pp. 5–6, 39):**
  * `Theorem_1_1_GeneralParams`, `Theorem_1_1_PaperRange`, `Theorem_1_1_Schedule` (Theorem 1.1)
  * `SatisfiesOverlapCond` (Definition 1.2) and `Proposition_SparseStack_Overlap`
* **Section 2.1 (Proof Overview Statements, pp. 9–14):**
  * `distSparse`, `IsFlatVec`, `IsSpikyVec` (Definition 2.1)
  * `Theorem_2_2_FlatPreservation` (Theorem 2.2)
  * `Theorem_2_3_CommonSupport` (Theorem 2.3)
  * `Lemma_2_4_IsolatedCrossTerm` and `Lemma_2_4_IsolatedCrossTerm_Submatrix` (Lemma 2.4)
  * `Theorem_2_5_HeavyPreservation` and `Theorem_2_5_HeavyPreservation_EvenBlocks` (Theorem 2.5)
* **Section 3 (Preserving Flat Vectors, pp. 20–25):**
  * `Fact_3_1_McDiarmid` (Fact 3.1, McDiarmid's bounded-differences inequality)
  * `Lemma_3_2_WeightedBernoulli` and `Lemma_3_2_PointwiseFlat` (Lemma 3.2)
  * `Lemma_3_3_LatticeRounding` (Lemma 3.3)
* **Section 4 (Common Support for Spiky Vectors, pp. 26–28):**
  * `Lemma_4_1_GaussianTruncation` (Lemma 4.1)
  * `Lemma_4_2_MinimaxSelection` (Lemma 4.2)
  * `Claim_4_3_MinimaxWeights` (Claim 4.3)
* **Section 5 (Bounding Cancellation from Complementary Coordinates, pp. 29–35):**
  * `Fact_5_1_HeidaryOffDiagMoment` (Fact 5.1, Heidary `[Hei26]` trace moment bound)
  * `Fact_5_2_ScalarVarMatrixBernstein` (Fact 5.2, matrix Bernstein expectation bound)
  * `Lemma_5_3_IidOpNorm` (Lemma 5.3)
  * `Claim_5_4_SingleBlockCoupling` (Claim 5.4)
  * `Lemma_5_5_CouplingJensen` (Lemma 5.5)
  * `Claim_5_6_SymmetricConvexDom` (Claim 5.6)
  * `Lemma_5_7_FullSketchMoment` (Lemma 5.7)
* **Section 6 (Preserving the Heavy Coordinates, pp. 36–38):**
  * `landsInBucket`, `IsIsolatedBucket` (Definition 6.1) and `IsGoodCoordMatrix` (Definition 6.2),
    together with `Theorem_Def61_Def62_Equivalence`
  * `Lemma_6_3_SingleGroup` and `Lemma_6_3_SingleGroup_Conditional` (Lemma 6.3)
  * `Lemma_6_4_TwoGroupIsolation` (Lemma 6.4, at exact `c₁ = 1 / 2304`)
-/

namespace OsiUb
namespace Spec

/-! ## 1. Linear-algebraic primitives and Definition 2.1 (Flat vs. Spiky Vectors) -/

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

/-- Squared `ℓ₂` distance `d_m(y)² = min_{|I| ≤ m} ∑_{i ∉ I} yᵢ²` from `y ∈ ℝ^n` to `m`-sparse
vectors (Definition 2.1, p. 9). -/
noncomputable def distSparseSq {n : ℕ} (m : ℕ) (y : Fin n → ℝ) : ℝ :=
  ⨅ I : {I : Finset (Fin n) // I.card ≤ m}, ∑ i ∈ (I.1)ᶜ, (y i) ^ 2

/-- **Definition 2.1 (Euclidean distance to `m`-sparse vectors, p. 9):**
`d_m(y) = √(min_{|I| ≤ m} ∑_{i ∉ I} yᵢ²)`. -/
noncomputable def distSparse {n : ℕ} (m : ℕ) (y : Fin n → ℝ) : ℝ :=
  Real.sqrt (distSparseSq m y)

/-- **Definition 2.1 (`(m, ε)`-flat vector, p. 9):** `d_m(y) ≥ ε`. -/
def IsFlatVec {n : ℕ} (m : ℕ) (ε : ℝ) (y : Fin n → ℝ) : Prop :=
  ε ≤ distSparse m y

/-- **Definition 2.1 (`(m, ε)`-spiky vector, p. 9):** `d_m(y) < ε`. -/
def IsSpikyVec {n : ℕ} (m : ℕ) (ε : ℝ) (y : Fin n → ℝ) : Prop :=
  distSparse m y < ε

/-- Coordinate restriction `v_I ∈ ℝ^n` retaining entries in `I` and zeroing out `Iᶜ`. -/
def coordVec {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ I then v i else 0

/-- Row-restricted matrix `Q_I ∈ ℝ^{n×r}` retaining rows in `I` and zeroing out rows outside `I`
(so `(Q_I)ᵀ (Q_I) = ∑_{i ∈ I} qᵢ qᵢᵀ`). -/
def coordRows {n r : ℕ} (I : Finset (Fin n)) (Q : Matrix (Fin n) (Fin r) ℝ) :
    Matrix (Fin n) (Fin r) ℝ :=
  fun i j => if i ∈ I then Q i j else 0

/-- Ambient zero-padded embedding of a submatrix `W ∈ ℝ^{|J|×d}` (`J ⊆ [n]`) into `ℝ^{n×d}`. -/
def embedSubmatrix {n d : ℕ} (J : Finset (Fin n)) (W : Matrix J (Fin d) ℝ) :
    Matrix (Fin n) (Fin d) ℝ :=
  fun i l => if h : i ∈ J then W ⟨i, h⟩ l else 0

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

/-- **Definition 1.2 (Overlap condition, p. 5):** `S ∈ ℝ^{n×k}` satisfies the overlap condition
with parameter `η` if `∑_{1 ≤ u < v ≤ n} 1{|supp(s_u) ∩ supp(s_v)| ≥ 2} ≤ η · n² / k`. -/
def SatisfiesOverlapCond {n k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (η : ℝ) : Prop :=
  (overlapPairCount S : ℝ) ≤ η * ((n : ℝ) ^ 2 / (k : ℝ))

/-- Entrywise Borel measurability of a random matrix `M : Ω_prob → ℝ^{n×k}` on a measurable space
`Ω_prob`. -/
def IsRandomMatrix {Ω_prob : Type} [MeasurableSpace Ω_prob] {n k : ℕ}
    (M : Ω_prob → Matrix (Fin n) (Fin k) ℝ) : Prop :=
  ∀ (i : Fin n) (j : Fin k), Measurable (fun ω => M ω i j)

/-- Isotropy `E[Ω Ωᵀ] = I_n` (Section 1.2, p. 5): every entry of `Ω Ωᵀ` is integrable under `P`
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
(Theorem 1.1, pp. 5, 39). -/
def IsOSI {Ω_prob : Type} [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob)
    {n k : ℕ} (M : Ω_prob → Matrix (Fin n) (Fin k) ℝ) (r : ℕ) (α : ℝ) : Prop :=
  IsOSIWithProb P M r α (19 / 20)

/-! ## 3. Finite probability laws and the SparseStack ensemble -/

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

/-- Valid probability mass function on a finite sample space `Ω`: non-negative weights summing
to `1`. -/
def IsFinitePmf {Ω : Type} [Fintype Ω] (p : Ω → ℝ) : Prop :=
  (∀ ω : Ω, 0 ≤ p ω) ∧ (∑ ω : Ω, p ω) = 1

/-- Expectation `∑_ω p(ω) f(ω)` under a finite PMF `p`. -/
def pmfExpectReal {Ω : Type} [Fintype Ω] (p : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, p ω * f ω

/-- Matrix expectation `∑_ω p(ω) • M(ω)` under a finite PMF `p`. -/
def pmfExpectMatrix {Ω : Type} [Fintype Ω] {m l : Type}
    (p : Ω → ℝ) (M : Ω → Matrix m l ℝ) : Matrix m l ℝ :=
  ∑ ω : Ω, p ω • M ω

/-- Valid per-coordinate probability mass functions `pmf i : α i → ℝ` for `N` independent random
variables `(Z₁, …, Z_N) ∈ ∏ᵢ αᵢ`. -/
def IsCoordPmf {N : ℕ} {α : Fin N → Type} [∀ i, Fintype (α i)]
    (pmf : ∀ i : Fin N, α i → ℝ) : Prop :=
  (∀ (i : Fin N) (a : α i), 0 ≤ pmf i a) ∧ ∀ i : Fin N, (∑ a : α i, pmf i a) = 1

/-- Product weight `∏ᵢ pmfᵢ(xᵢ)` of a configuration `x ∈ ∀ i : Fin N, α i`. -/
def prodWeight {N : ℕ} {α : Fin N → Type} (pmf : ∀ i : Fin N, α i → ℝ)
    (x : ∀ i : Fin N, α i) : ℝ :=
  ∏ i : Fin N, pmf i (x i)

/-- Real expectation under the finite product distribution `∏ᵢ pmfᵢ`. -/
def prodExpectReal {N : ℕ} {α : Fin N → Type} [∀ i, Fintype (α i)]
    (pmf : ∀ i : Fin N, α i → ℝ) (f : (∀ i : Fin N, α i) → ℝ) : ℝ :=
  ∑ x : (∀ i : Fin N, α i), prodWeight pmf x * f x

/-- Event probability under the finite product distribution `∏ᵢ pmfᵢ`. -/
noncomputable def prodProb {N : ℕ} {α : Fin N → Type} [∀ i, Fintype (α i)]
    (pmf : ∀ i : Fin N, α i → ℝ) (E : (∀ i : Fin N, α i) → Prop) : ℝ :=
  ∑ x : (∀ i : Fin N, α i),
    prodWeight pmf x * @ite ℝ (E x) (Classical.propDecidable (E x)) 1 0

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

/-! ## 4. Section 1.2 Main Upper-Bound Results & Overlap Proposition -/

/-- **Theorem 1.1 (General `(ζ, b)` form, pp. 5, 39):** For `C = constC`, `K = constK`, and
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

/-- **Theorem 1.1 (Existential universal-constant `Θ(√log r)` / `Θ(r)` form, pp. 5, 39):**
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

/-- **Theorem 1.1 (Canonical schedule `ζ = numBlocks r`, `b = numBuckets r`, pp. 5, 39):**
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

/-- **Proposition (SparseStack satisfies Definition 1.2, Section 1.2, pp. 5–6):**
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

/-! ## 5. Auxiliary Matrix, Polytope, Coupling, and Isolation Definitions (Sections 2–6) -/

/-- Compact convex weight polytope `W = {w ∈ [0, 1]^n : ∑ᵢ wᵢ ≤ B_sum}` (Section 4, p. 27). -/
def weightPolytope (n : ℕ) (B_sum : ℝ) : Set (Fin n → ℝ) :=
  {w : Fin n → ℝ | (∀ i : Fin n, 0 ≤ w i ∧ w i ≤ 1) ∧ (∑ i : Fin n, w i) ≤ B_sum}

/-- Weighted row-Gram matrix `D(w) = ∑ᵢ (1 - wᵢ) vᵢ vᵢᵀ` (Section 4, p. 27). -/
def weightedRowGram {n r : ℕ} (V : Matrix (Fin n) (Fin r) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  ∑ i : Fin n, (1 - w i) • Matrix.vecMulVec (V i) (V i)

/-- Entry encoding for the independent-entry `{±1, 0}` model of Fact 5.1 (p. 30): on `Fin (2B)`,
`0 ↦ +1`, `1 ↦ -1`, and `u ≥ 2 ↦ 0` (probabilities `1/(2B), 1/(2B), 1 - 1/B`). -/
def iidTernaryEntry {B : ℕ} (u : Fin (2 * B)) : ℝ :=
  if u.val = 0 then 1 else if u.val = 1 then -1 else 0

/-- Sample space for an `m × n` independent-entry `{±1, 0}` matrix with non-zero probability `1/B`
(Fact 5.1 & Lemma 5.3, pp. 30–31). -/
abbrev IidTernarySample (m n B : ℕ) : Type :=
  Fin m → Fin n → Fin (2 * B)

/-- Matrix `X ∈ {-1, 0, 1}^{m×n}` associated with `ω ∈ IidTernarySample m n B`. -/
def iidTernaryMatrix {m n B : ℕ} (ω : IidTernarySample m n B) : Matrix (Fin m) (Fin n) ℝ :=
  fun ℓ j => iidTernaryEntry (ω ℓ j)

/-- Hollow off-diagonal Gram sum `F = a⁻¹ ∑_{ℓ=1}^m ∑_{j ≠ j'} X_{ℓ,j} X_{ℓ,j'} w_j w_{j'}ᵀ`
of Fact 5.1 (Eq. (26), p. 30). -/
noncomputable def iidOffDiagGram (a B n d : ℕ) (W : Matrix (Fin n) (Fin d) ℝ)
    (ω : IidTernarySample (a * B) n B) : Matrix (Fin d) (Fin d) ℝ :=
  (a : ℝ)⁻¹ • ∑ ℓ : Fin (a * B), ∑ j : Fin n, ∑ j' ∈ Finset.univ.erase j,
    (iidTernaryMatrix ω ℓ j * iidTernaryMatrix ω ℓ j') • Matrix.vecMulVec (W j) (W j')

/-- Ternary outcome encoding `Fin 3 → {-1, 0, 1}` (`0 ↦ -1`, `1 ↦ 0`, `2 ↦ +1`) for Claim 5.4. -/
def ternaryVal (t : Fin 3) : ℝ :=
  if t.val = 0 then -1 else if t.val = 1 then 0 else 1

/-- Single-coordinate marginal PMF on `Fin 3` (`{-1, 0, 1}` with probs `1/(2b), 1 - 1/b, 1/(2b)`)
in Claim 5.4 (p. 32). -/
noncomputable def ternaryCoordMass (b : ℕ) (t : Fin 3) : ℝ :=
  if t.val = 1 then 1 - 1 / (b : ℝ) else 1 / (2 * (b : ℝ))

/-- Single-block coupling constant `c_b = (1 - (1 - 1/b)^b)⁻¹` of Claim 5.4 (Eq. (31), p. 32). -/
noncomputable def couplingCB (b : ℕ) : ℝ :=
  (1 - (1 - 1 / (b : ℝ)) ^ b)⁻¹

/-- Sample space for the `ζ` independent `|I| × |J|` ternary blocks `x_{t,i,j}` in Lemma 5.5
(Eq. (33), p. 32). -/
abbrev IidBlockTernarySample {n : ℕ} (ζ : ℕ) (I J : Finset (Fin n)) (b : ℕ) : Type :=
  Fin ζ → I → J → Fin (2 * b)

/-- Aggregate `|I| × |J|` matrix `U` with independent entries `U_{i,j} = ζ⁻¹ ∑_{t=1}^ζ x_{t,i,j}`
in Lemma 5.5 (Eq. (32)–(33), p. 32). -/
noncomputable def aggSubmatrix {n : ℕ} (ζ : ℕ) (I J : Finset (Fin n)) (b : ℕ)
    (x : IidBlockTernarySample ζ I J b) : Matrix I J ℝ :=
  fun i j => (ζ : ℝ)⁻¹ * ∑ t : Fin ζ, iidTernaryEntry (x t i j)

/-- Number of coordinates of `I` hashed to bucket `u` in block `t` of `ω`. -/
def bucketLoad {ζ b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample ζ b n)
    (t : Fin ζ) (u : Fin b) : ℕ :=
  (I.filter (fun i => ω.1 t i = u)).card

/-- Number of blocks `t ∈ [ζ]` in which `i ∈ [n]` lands in a bucket containing no other coordinate
of `I` (`a_i` in Lemmas 6.3 and 6.4, pp. 36–37). -/
def isolatedBlockCount {ζ b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample ζ b n)
    (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun t : Fin ζ => ∀ j ∈ I, j ≠ i → ω.1 t j ≠ ω.1 t i)).card

/-- Diagonal selector matrix on `Fin (ζ * b)` retaining output coordinates `(t, u)` that contain
exactly one element of `I` (`T` in Lemma 2.4, pp. 12, 29, 33). -/
def retainUniqueMatrix {ζ b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample ζ b n) :
    Matrix (Fin (ζ * b)) (Fin (ζ * b)) ℝ :=
  Matrix.diagonal (fun j =>
    let p := finProdFinEquiv.symm j
    if bucketLoad I ω p.1 p.2 = 1 then 1 else 0)

/-- Head-background sample merge: coordinates in `I` (all blocks and signs) come from `ω₀`, while
coordinates outside `I` come from `ω` (used to express conditioning on `Ω_I` in Lemmas 2.4, 5.5,
and 6.3). -/
def mergeHeadSample {ζ b n : ℕ} (I : Finset (Fin n)) (ω₀ ω : SketchSample ζ b n) :
    SketchSample ζ b n :=
  (fun t i => if i ∈ I then ω₀.1 t i else ω.1 t i,
   fun t i => if i ∈ I then ω₀.2 t i else ω.2 t i)

/-- Ambient retained cross-term matrix `(Ω̃_I) (Ω̃_{Iᶜ}ᵀ V) ∈ ℝ^{n×d}` (zero outside `I`). -/
noncomputable def retainedCrossGram {ζ b n d : ℕ} (I : Finset (Fin n))
    (V : Matrix (Fin n) (Fin d) ℝ) (ω : SketchSample ζ b n) : Matrix (Fin n) (Fin d) ℝ :=
  let T := retainUniqueMatrix I ω
  let Phi := (sparseStackOmega ω).transpose
  (T * Phi * Matrix.diagonal (fun i : Fin n => if i ∈ I then (1 : ℝ) else 0)).transpose *
    (T * Phi * V)

/-- Exact `|I| × d` submatrix cross-term `Ω̃_I Ω̃_Jᵀ W ∈ ℝ^{|I|×d}` of Lemma 2.4 and Lemma 5.5
for coordinate sets `I, J ⊆ [n]` and `W ∈ ℝ^{|J|×d}`. -/
noncomputable def isolatedSubmatrixCross {ζ b n d : ℕ} (I J : Finset (Fin n))
    (W : Matrix J (Fin d) ℝ) (ω : SketchSample ζ b n) : Matrix I (Fin d) ℝ :=
  fun i l => retainedCrossGram I (embedSubmatrix J W) ω i.1 l

/-- Column-restricted transposed sketch `Ω_{ζ,b,S}ᵀ ∈ ℝ^{(ζ·b)×|S|}` for `S ⊆ [n]` (Section 6). -/
noncomputable def sketchSubmatrixCols {ζ b n : ℕ} (S : Finset (Fin n))
    (ω : SketchSample ζ b n) : Matrix (Fin (ζ * b)) S ℝ :=
  fun r_row i => (sparseStackOmega ω).transpose r_row i.1

/-- **Definition 6.1 (Column lands in bucket, p. 36):** For `A = Ωᵀ ∈ ℝ^{k×N}`, column `i` lands
in bucket (row) `r_row` iff `A r_row i ≠ 0`. -/
def landsInBucket {k : ℕ} {N : Type} (A : Matrix (Fin k) N ℝ) (i : N) (r_row : Fin k) : Prop :=
  A r_row i ≠ 0

/-- **Definition 6.1 (Isolated bucket, p. 36):** Bucket (row) `r_row` of `A = Ωᵀ ∈ ℝ^{k×N}` is
isolated iff `r_row` has a single non-zero entry (`|{i : A r_row i ≠ 0}| = 1`). -/
noncomputable def IsIsolatedBucket {k : ℕ} {N : Type} [Fintype N]
    (A : Matrix (Fin k) N ℝ) (r_row : Fin k) : Prop :=
  ((Set.toFinite {i : N | A r_row i ≠ 0}).toFinset).card = 1

/-- Set of buckets (rows) in which column `i` of `A = Ωᵀ` lands (Definition 6.1–6.2, p. 36). -/
noncomputable def landedBuckets {k : ℕ} {N : Type} (A : Matrix (Fin k) N ℝ) (i : N) :
    Finset (Fin k) :=
  (Set.toFinite {r_row : Fin k | landsInBucket A i r_row}).toFinset

/-- Subset of buckets in which column `i` of `A = Ωᵀ` lands that are isolated (Definition 6.2). -/
noncomputable def isolatedLandedBuckets {k : ℕ} {N : Type} [Fintype N]
    (A : Matrix (Fin k) N ℝ) (i : N) : Finset (Fin k) :=
  (Set.toFinite {r_row : Fin k | landsInBucket A i r_row ∧ IsIsolatedBucket A r_row}).toFinset

/-- **Definition 6.2 (Good coordinate, p. 36):** Coordinate `i` is good for `A = Ωᵀ ∈ ℝ^{k×N}`
iff at least an `11/12` fraction of the buckets `i` lands in are isolated. -/
def IsGoodCoordMatrix {k : ℕ} {N : Type} [Fintype N]
    (A : Matrix (Fin k) N ℝ) (i : N) : Prop :=
  (11 / 12 : ℝ) * ((landedBuckets A i).card : ℝ) ≤ ((isolatedLandedBuckets A i).card : ℝ)

/-! ## 6. Section 2.1 Overview Theorems & Lemma 2.4 -/

/-- **Theorem 2.2 (Uniform preservation of flat vectors, pp. 10, 24):**
There exists a universal constant `c_lam > 0` such that for every `ε ∈ (0, 1)` and `δ_loc ∈ (0, 1)`,
there exist constants `λ ≥ c_lam ε`, `C_loc ≥ 1`, `M_loc ≥ 1`, and `r₀ ≥ 1` such that for all
`n ≥ r ≥ r₀`, `1 ≤ ζ ≤ r`, `b ≥ 1`, `k = ζ b ≥ C_loc r`, `m ≥ M_loc r / ζ`, and every isometry
`Q ∈ ℝ^{n×r}`, `P(∃ x ∈ S^{r-1}, IsFlatVec m ε (Q x) ∧ ‖Ω_{ζ,b}ᵀ Q x‖ < λ) ≤ δ_loc`. -/
def Theorem_2_2_FlatPreservation : Prop :=
  ∃ c_lam : ℝ, 0 < c_lam ∧
    ∀ (ε δ_loc : ℝ), 0 < ε → ε < 1 → 0 < δ_loc → δ_loc < 1 →
      ∃ (lam C_loc M_loc : ℝ) (r₀ : ℕ), c_lam * ε ≤ lam ∧ 1 ≤ C_loc ∧ 1 ≤ M_loc ∧ 1 ≤ r₀ ∧
        ∀ (n r ζ b m : ℕ), r₀ ≤ r → r ≤ n → 1 ≤ ζ → ζ ≤ r → 1 ≤ b →
          C_loc * (r : ℝ) ≤ ((ζ * b : ℕ) : ℝ) →
          M_loc * (r : ℝ) ≤ (ζ : ℝ) * (m : ℝ) →
          ∀ Q : Matrix (Fin n) (Fin r) ℝ, IsIsometry Q →
            uniformProb (SketchSample ζ b n)
              (fun ω => ∃ x : Fin r → ℝ,
                vecSqNorm x = 1 ∧ IsFlatVec m ε (Q.mulVec x) ∧
                  vecSqNorm (((sparseStackOmega ω).transpose * Q).mulVec x) < lam ^ 2) ≤ δ_loc

/-- **Theorem 2.3 (Common support extraction for spiky vectors, pp. 11, 28):**
For any `n, r, k, m : ℕ`, `ε > 0`, `λ > 0`, isometry `Q ∈ ℝ^{n×r}`, and matrix `X ∈ ℝ^{k×r}`, if
`IsFlatVec m ε (Q x) ∧ ‖x‖ = 1 ⇒ ‖X x‖ ≥ λ`, then there exists `I ⊆ [n]` with `|I| ≤ 8 m` such
that `Q_{Iᶜ}ᵀ Q_{Iᶜ} ⪯ (8/3) ε² I_r + (8 / (3 λ²)) Xᵀ X`. -/
def Theorem_2_3_CommonSupport : Prop :=
  ∀ (n r k m : ℕ) (ε lam : ℝ), 0 < ε → 0 < lam →
    ∀ (Q : Matrix (Fin n) (Fin r) ℝ) (X : Matrix (Fin k) (Fin r) ℝ),
      IsIsometry Q →
      (∀ x : Fin r → ℝ, vecSqNorm x = 1 → IsFlatVec m ε (Q.mulVec x) →
        lam ^ 2 ≤ vecSqNorm (X.mulVec x)) →
      ∃ I : Finset (Fin n), I.card ≤ 8 * m ∧
        LoewnerLe ((coordRows Iᶜ Q).transpose * coordRows Iᶜ Q)
          (((8 / 3 : ℝ) * ε ^ 2) • (1 : Matrix (Fin r) (Fin r) ℝ) +
            ((8 / (3 * lam ^ 2) : ℝ) • (X.transpose * X)))

/-- **Lemma 2.4 (Cross-term operator norm on isolated buckets, ambient off-`I` form, pp. 12, 29, 33):**
There exists a universal constant `C_cg > 0` such that for `ζ ≥ 1`, `b ≥ 2 ζ`, `I ⊆ [n]` with
`N = |I| ≥ 1`, any fixed isometry `V ∈ ℝ^{n×d}` (`d ≥ 1`) supported off `I`, any integer
`p ≥ max{1, log(2 d)}` (`D_p = d + 2 p + 1`), and any head configuration `ω₀` of `I`,
`E[‖Ω̃_I Ω̃_{Iᶜ}ᵀ V‖ | Ω_I = ω₀] ≤ C_cg (√((N + D_p)/(ζ b) + (p + 1)/ζ²) + √(N d / (ζ² b³) · C(ζ,3)))`,
and the cross-term vanishes whenever `I = ∅` or `d = 0`. -/
def Lemma_2_4_IsolatedCrossTerm : Prop :=
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

/-- **Lemma 2.4 (Cross-term operator norm, disjoint `I, J ⊆ [n]` submatrix `W ∈ ℝ^{|J|×d}` form,
pp. 12, 29, 33):** Exact `|I| × d` matrix formulation for disjoint coordinate sets `I, J ⊆ [n]`
and submatrix isometry `W ∈ ℝ^{|J|×d}` (`Wᵀ W = I_d`), including triviality at `I = ∅` or `d = 0`. -/
def Lemma_2_4_IsolatedCrossTerm_Submatrix : Prop :=
  ∃ C_cg : ℝ, 0 < C_cg ∧
    (∀ (ζ b n : ℕ) (I J : Finset (Fin n)) (ω : SketchSample ζ b n) (W : Matrix J (Fin 0) ℝ),
      spectralNorm (isolatedSubmatrixCross I J W ω) = 0) ∧
    (∀ (ζ b n d : ℕ) (J : Finset (Fin n)) (ω : SketchSample ζ b n) (W : Matrix J (Fin d) ℝ),
      spectralNorm (isolatedSubmatrixCross ∅ J W ω) = 0) ∧
    ∀ (ζ b n d p : ℕ), 1 ≤ ζ → 2 * ζ ≤ b → 1 ≤ d → 1 ≤ p →
      Real.log (2 * (d : ℝ)) ≤ (p : ℝ) →
      ∀ (I J : Finset (Fin n)) (W : Matrix J (Fin d) ℝ),
        Disjoint I J → 1 ≤ I.card → IsIsometry W →
        ∀ ω₀ : SketchSample ζ b n,
          uniformMeanReal (SketchSample ζ b n)
            (fun ω => spectralNorm (isolatedSubmatrixCross I J W (mergeHeadSample I ω₀ ω))) ≤
            C_cg * (Real.sqrt (((I.card : ℝ) + ((d : ℝ) + 2 * (p : ℝ) + 1)) / ((ζ * b : ℕ) : ℝ) +
                ((p : ℝ) + 1) / (ζ : ℝ) ^ 2) +
              Real.sqrt ((I.card : ℝ) * (d : ℝ) / ((ζ : ℝ) ^ 2 * (b : ℝ) ^ 3) *
                (Nat.choose ζ 3 : ℝ)))

/-- **Theorem 2.5 (Heavy-coordinate preservation for all integer `ζ`, pp. 14, 38):**
For every `t₀ ∈ (0, 1/4)` and `δ_rep ∈ (0, 1)`, there exist constants
`β ≥ (1/3)(11/12 - 2 t₀) > 0`, `C⋆ > 0`, and `K⋆ > 0` such that for all `n ≥ r ≥ 2`, all integers
`ζ ≥ C⋆ √log(e r)` and `k = ζ b ≥ K⋆ r`, every isometry `Q ∈ ℝ^{n×r}`, and every `I ⊆ [n]` with
`|I| ≤ min{r, b / 16}`, `Y = Ω_{ζ,b}ᵀ Q` satisfies with probability at least `1 - δ_rep` both
`‖Y x‖² ≥ β ‖(Q x)_I‖² - t₀ ‖(Q x)_{Iᶜ}‖²` for all `x ∈ ℝ^r` and equivalently
`Yᵀ Y + (β + t₀) Q_{Iᶜ}ᵀ Q_{Iᶜ} ⪰ β I_r`. -/
def Theorem_2_5_HeavyPreservation : Prop :=
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

/-- **Theorem 2.5 (Even block count `ζ = 2 ζ₁`, exact `β = 11 / 24 - t₀`, pp. 38–39):**
When `ζ = 2 ζ₁` splits into two equal `ζ₁`-block groups as on p. 38 (`ζ₁ = ζ / 2`), Theorem 2.5
holds with the exact printed constant `β = 11 / 24 - t₀ > 0` (p. 39, line 2438). -/
def Theorem_2_5_HeavyPreservation_EvenBlocks : Prop :=
  ∀ (t₀ δ_rep : ℝ), 0 < t₀ → t₀ < 1 / 4 → 0 < δ_rep → δ_rep < 1 →
    let β : ℝ := 11 / 24 - t₀
    0 < β ∧
    ∃ (C_star K_star : ℝ), 0 < C_star ∧ 0 < K_star ∧
      ∀ (n r ζ₁ b : ℕ), 2 ≤ r → r ≤ n →
        C_star * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))) ≤ ((2 * ζ₁ : ℕ) : ℝ) →
        K_star * (r : ℝ) ≤ (((2 * ζ₁) * b : ℕ) : ℝ) →
        ∀ (Q : Matrix (Fin n) (Fin r) ℝ) (I : Finset (Fin n)),
          IsIsometry Q → I.card ≤ r → 16 * I.card ≤ b →
          (1 - δ_rep) ≤ uniformProb (SketchSample (2 * ζ₁) b n)
            (fun ω =>
              let Y := (sparseStackOmega ω).transpose * Q
              (∀ x : Fin r → ℝ,
                β * vecSqNorm (coordVec I (Q.mulVec x)) -
                    t₀ * vecSqNorm (coordVec Iᶜ (Q.mulVec x)) ≤
                  vecSqNorm (Y.mulVec x)) ∧
                LoewnerLe (β • (1 : Matrix (Fin r) (Fin r) ℝ))
                  (Y.transpose * Y +
                    (β + t₀) • ((coordRows Iᶜ Q).transpose * coordRows Iᶜ Q)))

/-! ## 7. Section 3 Statements: McDiarmid, Pointwise Flat Bound, and Lattice Rounding Net -/

/-- **Fact 3.1 (McDiarmid's bounded-differences inequality `[McD89]`, p. 20, Eq. (17)):**
For independent random variables `Z₁, …, Z_N` on arbitrary finite spaces `α₁, …, α_N` with PMFs
`pmfᵢ` (`IsCoordPmf pmf`), if `f : (∏ᵢ αᵢ) → ℝ` has bounded differences `≤ cᵢ` (`cᵢ ≥ 0`,
`∑ᵢ cᵢ² > 0`), then for every `t ≥ 0` both `P(f - E[f] ≥ t) ≤ exp(-2 t² / ∑ᵢ cᵢ²)` and
`P(f - E[f] ≤ -t) ≤ exp(-2 t² / ∑ᵢ cᵢ²)`. -/
def Fact_3_1_McDiarmid : Prop :=
  ∀ (N : ℕ) (α : Fin N → Type) [∀ i, Fintype (α i)] (pmf : ∀ i : Fin N, α i → ℝ),
    IsCoordPmf pmf →
    ∀ (f : (∀ i : Fin N, α i) → ℝ) (c : Fin N → ℝ),
      (∀ i : Fin N, 0 ≤ c i) →
      0 < (∑ i : Fin N, (c i) ^ 2) →
      (∀ (i : Fin N) (x : ∀ j : Fin N, α j) (z' : α i),
        |f (Function.update x i z') - f x| ≤ c i) →
      ∀ t : ℝ, 0 ≤ t →
        prodProb pmf (fun x => t ≤ f x - prodExpectReal pmf f) ≤
            Real.exp (-2 * t ^ 2 / (∑ i : Fin N, (c i) ^ 2)) ∧
          prodProb pmf (fun x => f x - prodExpectReal pmf f ≤ -t) ≤
            Real.exp (-2 * t ^ 2 / (∑ i : Fin N, (c i) ^ 2))

/-- **Weighted Bernoulli lower-tail helper in Lemma 3.2's proof (pp. 22–23):**
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

/-- **Lemma 3.2 (Pointwise lower bound for flat tail vectors, p. 20):**
There exist universal constants `c₀, c_sb > 0` such that for any `h, z ∈ ℝ^n` with disjoint
supports, `a > 0`, `‖z‖₂ = 1`, `1 ≤ D ≤ b`, and `‖z‖_∞² ≤ D⁻¹`, a `ζ`-block SparseStack satisfies
`P(‖Ω_{ζ,b}ᵀ (h + a z)‖₂ < c₀ a) ≤ 2 exp(- c_sb ζ D)`. -/
def Lemma_3_2_PointwiseFlat : Prop :=
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

/-- **Lemma 3.3 (Unbiased lattice rounding net, p. 23):**
For every `r ≥ 1` and `0 < η < 1`, there exists a finite set `N_η ⊂ (1 + η) B₂^r` of cardinality
`|N_η| ≤ (16 / η)^r` such that for every real matrix `T ∈ ℝ^{k×r}` and every unit vector
`x ∈ S^{r-1}`, some `y ∈ N_η` satisfies `‖x - y‖₂ ≤ η` and `‖T(x - y)‖₂² ≤ (η² / (4 r)) ‖T‖_F²`. -/
def Lemma_3_3_LatticeRounding : Prop :=
  ∀ (r : ℕ) (η : ℝ), 1 ≤ r → 0 < η → η < 1 →
    ∃ N_net : Finset (Fin r → ℝ),
      (N_net.card : ℝ) ≤ (16 / η) ^ r ∧
        (∀ y ∈ N_net, vecSqNorm y ≤ (1 + η) ^ 2) ∧
        ∀ (k : ℕ) (T : Matrix (Fin k) (Fin r) ℝ) (x : Fin r → ℝ),
          vecSqNorm x = 1 →
          ∃ y ∈ N_net,
            vecSqNorm (x - y) ≤ η ^ 2 ∧
              vecSqNorm (T.mulVec (x - y)) ≤ (η ^ 2 / (4 * (r : ℝ))) * frobSq T

/-! ## 8. Section 4 Statements: Gaussian Truncation, Minimax Selection, and Claim 4.3 -/

/-- **Lemma 4.1 (Truncation lower bound for Gaussian / fourth-moment vectors, p. 26):**
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

/-- **Lemma 4.2 (Minimax extraction of a single common coordinate set, p. 27):**
Let `V ∈ ℝ^{n×r}`, `H ⪰ 0` (`r × r`), and `m : ℕ`. If `d_m(V x)² ≤ xᵀ H x` for all `x ∈ ℝ^r`,
then there exists `I ⊆ [n]` with `|I| ≤ 8 m` such that `V_{Iᶜ}ᵀ V_{Iᶜ} ⪯ (8/3) H`. -/
def Lemma_4_2_MinimaxSelection : Prop :=
  ∀ (n r m : ℕ) (V : Matrix (Fin n) (Fin r) ℝ) (H : Matrix (Fin r) (Fin r) ℝ),
    H.PosSemidef →
    (∀ x : Fin r → ℝ, distSparseSq m (V.mulVec x) ≤ dotProduct x (H.mulVec x)) →
    ∃ I : Finset (Fin n), I.card ≤ 8 * m ∧
      LoewnerLe ((coordRows Iᶜ V).transpose * coordRows Iᶜ V) ((8 / 3 : ℝ) • H)

/-- **Claim 4.3 (Existence of a single minimax weight vector `w ∈ W`, p. 27, Eqs. (22)–(25)):**
1. (**Minimax duality step, Eq. (22) ⇒ Claim 4.3**): For any `n, r : ℕ`, `B_sum ≥ 0`,
   `V ∈ ℝ^{n×r}`, and `H ⪰ 0`, if for every `R ⪰ 0` with `tr R = 1` there exists
   `w ∈ weightPolytope n B_sum` with `tr(R (D(w) - (4/3) H)) ≤ 0`, then there exists a single
   `w ∈ weightPolytope n B_sum` with `D(w) ⪯ (4/3) H`.
2. (**In the setting of Lemma 4.2**): Whenever `H ⪰ 0` and `d_m(V x)² ≤ xᵀ H x` for all `x ∈ ℝ^r`,
   there exists `w ∈ weightPolytope n (4 m)` such that `D(w) ⪯ (4/3) H`. -/
def Claim_4_3_MinimaxWeights : Prop :=
  (∀ (n r : ℕ) (B_sum : ℝ), 0 ≤ B_sum →
    ∀ (V : Matrix (Fin n) (Fin r) ℝ) (H : Matrix (Fin r) (Fin r) ℝ),
      H.PosSemidef →
      (∀ R : Matrix (Fin r) (Fin r) ℝ, R.PosSemidef → R.trace = 1 →
        ∃ w ∈ weightPolytope n B_sum,
          (R * (weightedRowGram V w - (4 / 3 : ℝ) • H)).trace ≤ 0) →
      ∃ w ∈ weightPolytope n B_sum, LoewnerLe (weightedRowGram V w) ((4 / 3 : ℝ) • H)) ∧
  (∀ (n r m : ℕ) (V : Matrix (Fin n) (Fin r) ℝ) (H : Matrix (Fin r) (Fin r) ℝ),
    H.PosSemidef →
    (∀ x : Fin r → ℝ, distSparseSq m (V.mulVec x) ≤ dotProduct x (H.mulVec x)) →
    ∃ w ∈ weightPolytope n (4 * (m : ℝ)), LoewnerLe (weightedRowGram V w) ((4 / 3 : ℝ) • H))

/-! ## 9. Section 5 Statements: Moments, Matrix Bernstein, Coupling, and Convex Order -/

/-- **Fact 5.1 (Heidary `[Hei26]` off-diagonal `2p`-th trace moment bound, p. 30, Eq. (27)):**
For `B ≥ 2`, `a ≥ 1`, `m = a B`, `d ≥ 1`, `p ≥ 1`, and any isometry `W ∈ ℝ^{n×d}`, the hollow
Gram matrix `F = iidOffDiagGram a B n d W ω` (`D_p = d + 2 p + 1`) satisfies
`E[tr(F^{2p})] ≤ d [3 (3 + √2) (√(D_p / m) + D_p / m + (2p + 1) / a)]^{2p}`. -/
def Fact_5_1_HeidaryOffDiagMoment : Prop :=
  ∀ (a B n d p : ℕ), 2 ≤ B → 1 ≤ a → 1 ≤ d → 1 ≤ p →
    ∀ W : Matrix (Fin n) (Fin d) ℝ, IsIsometry W →
      uniformMeanReal (IidTernarySample (a * B) n B)
        (fun ω => ((iidOffDiagGram a B n d W ω) ^ (2 * p)).trace) ≤
        (d : ℝ) * (3 * (3 + Real.sqrt 2) *
          (Real.sqrt (((d : ℝ) + 2 * (p : ℝ) + 1) / ((a * B : ℕ) : ℝ)) +
            ((d : ℝ) + 2 * (p : ℝ) + 1) / ((a * B : ℕ) : ℝ) +
            (2 * (p : ℝ) + 1) / (a : ℝ))) ^ (2 * p)

/-- **Fact 5.2 (Matrix Bernstein expectation bound, pp. 30–31, Eq. (28)):**
For independent, centered, symmetric `d × d` (`d ≥ 1`) random matrices `R₁, …, R_m` on finite
spaces `α₁, …, α_m` (`IsCoordPmf pmf`) satisfying `‖R_j‖ ≤ ℓ` (`ℓ ≥ 0`) and scalar variance
proxies `E[R_j²] ⪯ v_j I_d` (`v_j ≥ 0`, `∑_j v_j ≤ v`),
`E[‖∑_j R_j‖] ≤ √(2 v log(2 d)) + (ℓ / 3) log(2 d)`. -/
def Fact_5_2_ScalarVarMatrixBernstein : Prop :=
  ∀ (m d : ℕ), 1 ≤ d →
    ∀ (α : Fin m → Type) [∀ j, Fintype (α j)] (pmf : ∀ j : Fin m, α j → ℝ),
      IsCoordPmf pmf →
      ∀ (R : ∀ j : Fin m, α j → Matrix (Fin d) (Fin d) ℝ) (v_coord : Fin m → ℝ) (v ℓ : ℝ),
        0 ≤ ℓ →
        (∀ j : Fin m, 0 ≤ v_coord j) →
        (∑ j : Fin m, v_coord j) ≤ v →
        (∀ (j : Fin m) (a : α j), (R j a).IsHermitian) →
        (∀ j : Fin m, pmfExpectMatrix (pmf j) (R j) = 0) →
        (∀ (j : Fin m) (a : α j), spectralNorm (R j a) ≤ ℓ) →
        (∀ j : Fin m,
          LoewnerLe (pmfExpectMatrix (pmf j) (fun a => (R j a) ^ 2))
            (v_coord j • (1 : Matrix (Fin d) (Fin d) ℝ))) →
        prodExpectReal pmf (fun x => spectralNorm (∑ j : Fin m, R j (x j))) ≤
          Real.sqrt (2 * v * Real.log (2 * (d : ℝ))) + (ℓ / 3) * Real.log (2 * (d : ℝ))

/-- **Lemma 5.3 (Expected squared operator norm in the independent-entry model, p. 31):**
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

/-- **Claim 5.4 (Single-block CountSketch / i.i.d. ternary coupling, p. 32, Eq. (31)):**
For every `b ≥ 1`, `c_b = couplingCB b` satisfies `1 ≤ c_b ≤ (1 - e⁻¹)⁻¹ < 2`, and there exists a
joint PMF `J` on `({-1, 0, 1}^b) × ([b] × {±1})` whose first marginal is the i.i.d. ternary vector
`η` with probabilities `1/(2b), 1 - 1/b, 1/(2b)`, whose second marginal is uniform on `[b] × {±1}`
(`ξ = σ e_u`), and whose conditional expectation satisfies `E[η | ξ] = c_b⁻¹ ξ` entrywise. -/
def Claim_5_4_SingleBlockCoupling : Prop :=
  (1 - Real.exp (-1))⁻¹ < 2 ∧
  ∀ b : ℕ, 1 ≤ b →
    1 ≤ couplingCB b ∧ couplingCB b ≤ (1 - Real.exp (-1))⁻¹ ∧
    ∃ J : ((Fin b → Fin 3) × (Fin b × Bool)) → ℝ,
      IsFinitePmf J ∧
      (∀ η : Fin b → Fin 3,
        (∑ ξ : Fin b × Bool, J (η, ξ)) = ∏ u : Fin b, ternaryCoordMass b (η u)) ∧
      (∀ ξ : Fin b × Bool,
        (∑ η : Fin b → Fin 3, J (η, ξ)) = 1 / (2 * (b : ℝ))) ∧
      ∀ (ξ : Fin b × Bool) (u' : Fin b),
        (∑ η : Fin b → Fin 3, J (η, ξ) * ternaryVal (η u')) /
            (∑ η : Fin b → Fin 3, J (η, ξ)) =
          (couplingCB b)⁻¹ * (if u' = ξ.1 then signValue ξ.2 else 0)

/-- **Lemma 5.5 (Conditional Jensen coupling bound for the isolated cross-term, p. 32, Eq. (32)):**
For any `ζ ≥ 1`, `b ≥ 1`, disjoint `I, J ⊆ [n]`, `W ∈ ℝ^{|J|×d}`, and head realization `ω₀`,
`E[‖Ω̃_I Ω̃_Jᵀ W‖ | Ω_{ζ,b,I} = ω₀] ≤ c_b E[‖U W‖]`, where `U ∈ ℝ^{|I|×|J|}` has i.i.d. entries
`U_{i,j} = ζ⁻¹ ∑_{t=1}^ζ x_{t,i,j}` with `x_{t,i,j} ∈ {-1, 0, 1}` of probs `1/(2b), 1-1/b, 1/(2b)`. -/
def Lemma_5_5_CouplingJensen : Prop :=
  ∀ (ζ b n d : ℕ), 1 ≤ ζ → 1 ≤ b →
    ∀ (I J : Finset (Fin n)) (W : Matrix J (Fin d) ℝ),
      Disjoint I J →
      ∀ ω₀ : SketchSample ζ b n,
        uniformMeanReal (SketchSample ζ b n)
          (fun ω => spectralNorm (isolatedSubmatrixCross I J W (mergeHeadSample I ω₀ ω))) ≤
          couplingCB b * uniformMeanReal (IidBlockTernarySample ζ I J b)
            (fun x => spectralNorm (aggSubmatrix ζ I J b x * W))

/-- **Claim 5.6 (Symmetric bounded convex dominance `E[φ(V)] ≤ E[φ(2 η_B)]`, p. 34, Eq. (42)):**
For any integer `B ≥ 2`, any symmetric real random variable `V` on a finite probability space
`(Ω, p)` (`IsFinitePmf p`) satisfying `|V| ≤ 2` everywhere and `E[|V|] ≤ 1 / B`, and every convex
function `φ : ℝ → ℝ`, `E[φ(V)] ≤ E[φ(2 η_B)] = (1 - 1/B) φ(0) + (1/(2B)) (φ(2) + φ(-2))`. -/
def Claim_5_6_SymmetricConvexDom : Prop :=
  ∀ B : ℕ, 2 ≤ B →
    ∀ (Ω : Type) [Fintype Ω] (p : Ω → ℝ),
      IsFinitePmf p →
      ∀ V : Ω → ℝ,
        (∀ ψ : ℝ → ℝ, pmfExpectReal p (fun ω => ψ (V ω)) = pmfExpectReal p (fun ω => ψ (-V ω))) →
        (∀ ω : Ω, |V ω| ≤ 2) →
        pmfExpectReal p (fun ω => |V ω|) ≤ 1 / (B : ℝ) →
        ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ →
          pmfExpectReal p (fun ω => φ (V ω)) ≤
              uniformMeanReal (Fin (2 * B)) (fun u => φ (2 * iidTernaryEntry u)) ∧
            uniformMeanReal (Fin (2 * B)) (fun u => φ (2 * iidTernaryEntry u)) =
              (1 - 1 / (B : ℝ)) * φ 0 + (1 / (2 * (B : ℝ))) * (φ 2 + φ (-2))

/-- **Lemma 5.7 (High-moment bound for the full SparseStack Gram error, p. 35, Eq. (47)):**
With `C_mom = 12 (3 + √2) > 0` (p. 35, line 2195), for any fixed isometry `U ∈ ℝ^{n×D}` (`D ≥ 1`),
`b ≥ 2`, `ζ ≥ 1`, and `p ≥ 1`, `G = Uᵀ Ω_{ζ,b} Ω_{ζ,b}ᵀ U` (`k = ζ b`) satisfies
`E[‖G - I_D‖^{2p}] ≤ D [C_mom (√((D + 2p + 1)/k) + (D + 2p + 1)/k + (2p + 1)/ζ)]^{2p}`. -/
def Lemma_5_7_FullSketchMoment : Prop :=
  let C_mom : ℝ := 12 * (3 + Real.sqrt 2)
  0 < C_mom ∧
    ∀ (ζ b n D p : ℕ), 1 ≤ ζ → 2 ≤ b → 1 ≤ D → 1 ≤ p →
      ∀ U : Matrix (Fin n) (Fin D) ℝ, IsIsometry U →
        uniformMeanReal (SketchSample ζ b n)
          (fun ω =>
            let A := (sparseStackOmega ω).transpose * U
            spectralNorm (A.transpose * A - 1) ^ (2 * p)) ≤
          (D : ℝ) * (C_mom * (Real.sqrt (((D : ℝ) + 2 * (p : ℝ) + 1) / ((ζ * b : ℕ) : ℝ)) +
            ((D : ℝ) + 2 * (p : ℝ) + 1) / ((ζ * b : ℕ) : ℝ) +
            (2 * (p : ℝ) + 1) / (ζ : ℝ))) ^ (2 * p)

/-! ## 10. Section 6 Statements: Definitions 6.1–6.2, Single-Group Lemma 6.3, and Two-Group Lemma 6.4 -/

/-- **Equivalence of Matrix-Entry Definitions 6.1 & 6.2 with Combinatorial Bucket Isolation
(Section 6, p. 36):** For any `ζ ≥ 1`, `b, n : ℕ`, `S ⊆ [n]`, and `ω ∈ SketchSample ζ b n`, on
`A = Ω_{ζ,b,S}ᵀ ∈ ℝ^{(ζ·b)×|S|}`:
1. Every row `r_row` corresponding to `(t, u)` is isolated (`IsIsolatedBucket A r_row`) iff
   `bucketLoad S ω t u = 1`;
2. Every coordinate `i ∈ S` lands in exactly `ζ` buckets (`(landedBuckets A i).card = ζ`), of
   which `isolatedBlockCount S ω i` are isolated;
3. `IsGoodCoordMatrix A i` holds iff `(11 / 12) ζ ≤ isolatedBlockCount S ω i`. -/
def Theorem_Def61_Def62_Equivalence : Prop :=
  ∀ (ζ b n : ℕ), 1 ≤ ζ →
    ∀ (S : Finset (Fin n)) (ω : SketchSample ζ b n),
      let A := sketchSubmatrixCols S ω
      (∀ r_row : Fin (ζ * b),
        IsIsolatedBucket A r_row ↔
          bucketLoad S ω (finProdFinEquiv.symm r_row).1 (finProdFinEquiv.symm r_row).2 = 1) ∧
      (∀ i : S,
        (landedBuckets A i).card = ζ ∧
          (isolatedLandedBuckets A i).card = isolatedBlockCount S ω i.1 ∧
          (IsGoodCoordMatrix A i ↔
            (11 / 12 : ℝ) * (ζ : ℝ) ≤ (isolatedBlockCount S ω i.1 : ℝ)))

/-- **Lemma 6.3 (Unconditional single-group norm preservation, exact paper form, p. 36, Eq. (49)):**
For any constants `t > 0` and `δ_rep > 0`, there exist `C₀, K₀ > 0` such that for all `n : ℕ`,
`r ≥ 2`, `b ≥ 2`, `ζ ≥ C₀ √log(e r)`, `k = ζ b ≥ K₀ r`, any `S ⊆ [n]` with `|S| ≤ r`, and any
isometry `W ∈ ℝ^{|Sᶜ|×d}` with `d ≤ 2 r`, with probability at least `1 - δ_rep / 4` over `Ω`,
simultaneously for all `h ∈ ℝ^{|S|}` and `f ∈ ℝ^d`:
`‖Ω_Sᵀ h + Ω_{Sᶜ}ᵀ W f‖² + t ‖f‖² ≥ (11/12 - t) ‖h_G‖² - t ‖h_B‖²`,
where `G = {i ∈ S : IsGoodCoordMatrix (Ω_Sᵀ) i}` (Definition 6.2) and `B = S \ G`. -/
def Lemma_6_3_SingleGroup : Prop :=
  ∀ (t δ_rep : ℝ), 0 < t → 0 < δ_rep →
    ∃ (C₀ K₀ : ℝ), 0 < C₀ ∧ 0 < K₀ ∧
      ∀ (n r ζ b d : ℕ), 2 ≤ r → 2 ≤ b →
        C₀ * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))) ≤ (ζ : ℝ) →
        K₀ * (r : ℝ) ≤ ((ζ * b : ℕ) : ℝ) →
        d ≤ 2 * r →
        ∀ (S : Finset (Fin n)) (W : Matrix (Sᶜ : Finset (Fin n)) (Fin d) ℝ),
          S.card ≤ r → IsIsometry W →
          (1 - δ_rep / 4) ≤ uniformProb (SketchSample ζ b n)
            (fun ω =>
              let Ω_S := sketchSubmatrixCols S ω
              let Ω_Sc := sketchSubmatrixCols Sᶜ ω
              let G : Finset S :=
                (Set.toFinite {i : S | IsGoodCoordMatrix Ω_S i}).toFinset
              let B : Finset S := Finset.univ \ G
              ∀ (h : S → ℝ) (f : Fin d → ℝ),
                (11 / 12 - t) * (∑ i ∈ G, (h i) ^ 2) - t * (∑ i ∈ B, (h i) ^ 2) ≤
                  vecSqNorm (Ω_S.mulVec h + (Ω_Sc * W).mulVec f) + t * vecSqNorm f)

/-- **Lemma 6.3 (Conditional-on-`Ω_S` moderate-sparsity form, p. 36):**
Conditioned on any fixed head realization `ω₀` of `S` in the moderate-sparsity window
`C₀ √log(e R) ≤ ζ₀ ≤ H₀ log(e R)` with `b ≥ 2 ζ₀`, the bound holds with probability at least
`1 - δ_rep / 4` over the independent background coordinates `Sᶜ`. -/
def Lemma_6_3_SingleGroup_Conditional : Prop :=
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

/-- **Lemma 6.4 (Two-group balls-into-bins isolation, pp. 37–38, exact `c₁ = 1 / 2304`):**
Fix `δ_rep ∈ (0, 1)` and `c₁ = 1 / 2304` (p. 38, line 2342). There exists `C_iso > 0` such that
for all `r ≥ 2`, `b ≥ 1`, `ζ₁ ≥ C_iso √log(e r)`, and `I ⊆ [n]` with `|I| ≤ min{r, b / 16}`:
(i) over Group 1 (`ω₁`), `|B| ≤ |I| exp(- c₁ ζ₁)` with probability at least `1 - δ_rep / 4`;
(ii) for every realization `ω₁` satisfying `|B| ≤ |I| exp(- c₁ ζ₁)`, over Group 2 (`ω₂`), every
`i ∈ B` lands in a bucket containing no other element of `B` in at least `(11/12) ζ₁` blocks with
probability at least `1 - δ_rep / 4`. -/
def Lemma_6_4_TwoGroupIsolation : Prop :=
  ∀ δ_rep : ℝ, 0 < δ_rep → δ_rep < 1 →
    let c₁ : ℝ := 1 / 2304
    ∃ C_iso : ℝ, 0 < C_iso ∧
      ∀ (n r ζ₁ b : ℕ), 2 ≤ r → 1 ≤ b →
        C_iso * Real.sqrt (Real.log (Real.exp 1 * (r : ℝ))) ≤ (ζ₁ : ℝ) →
        ∀ I : Finset (Fin n), I.card ≤ r → 16 * I.card ≤ b →
          let B_of : SketchSample ζ₁ b n → Finset (Fin n) :=
            fun ω₁ => I \ I.filter
              (fun i => (11 / 12 : ℝ) * (ζ₁ : ℝ) ≤ (isolatedBlockCount I ω₁ i : ℝ))
          ((1 - δ_rep / 4) ≤ uniformProb (SketchSample ζ₁ b n)
            (fun ω₁ => ((B_of ω₁).card : ℝ) ≤ (I.card : ℝ) * Real.exp (-c₁ * (ζ₁ : ℝ)))) ∧
          (∀ ω₁ : SketchSample ζ₁ b n,
            ((B_of ω₁).card : ℝ) ≤ (I.card : ℝ) * Real.exp (-c₁ * (ζ₁ : ℝ)) →
            (1 - δ_rep / 4) ≤ uniformProb (SketchSample ζ₁ b n)
              (fun ω₂ => ∀ i ∈ B_of ω₁,
                (11 / 12 : ℝ) * (ζ₁ : ℝ) ≤ (isolatedBlockCount (B_of ω₁) ω₂ i : ℝ)))

/-! ## 11. Complete Conjunction of All 28 Upper-Bound Statements (Sections 1–7) -/

/-- Conjunction of all 28 upper-bound theorems, propositions, lemmas, claims, and facts across
Sections 1–7 of `constant_injectivity_sparsestack-2.pdf`. -/
def AllUpperBoundTheorems : Prop :=
  Theorem_1_1_GeneralParams ∧
    Theorem_1_1_PaperRange ∧
    Theorem_1_1_Schedule ∧
    Proposition_SparseStack_Overlap ∧
    Theorem_2_2_FlatPreservation ∧
    Theorem_2_3_CommonSupport ∧
    Lemma_2_4_IsolatedCrossTerm ∧
    Lemma_2_4_IsolatedCrossTerm_Submatrix ∧
    Theorem_2_5_HeavyPreservation ∧
    Theorem_2_5_HeavyPreservation_EvenBlocks ∧
    Fact_3_1_McDiarmid ∧
    Lemma_3_2_WeightedBernoulli ∧
    Lemma_3_2_PointwiseFlat ∧
    Lemma_3_3_LatticeRounding ∧
    Lemma_4_1_GaussianTruncation ∧
    Lemma_4_2_MinimaxSelection ∧
    Claim_4_3_MinimaxWeights ∧
    Fact_5_1_HeidaryOffDiagMoment ∧
    Fact_5_2_ScalarVarMatrixBernstein ∧
    Lemma_5_3_IidOpNorm ∧
    Claim_5_4_SingleBlockCoupling ∧
    Lemma_5_5_CouplingJensen ∧
    Claim_5_6_SymmetricConvexDom ∧
    Lemma_5_7_FullSketchMoment ∧
    Theorem_Def61_Def62_Equivalence ∧
    Lemma_6_3_SingleGroup ∧
    Lemma_6_3_SingleGroup_Conditional ∧
    Lemma_6_4_TwoGroupIsolation

/-! ## 12. Non-vacuity and sanity checks (`0 sorry`) -/

/-- Sanity check 1: `constAlpha ∈ (10⁻⁴, 1)`. -/
example : (1 / 10000 : ℝ) < constAlpha ∧ constAlpha < 1 := by
  unfold constAlpha
  norm_num

/-- Sanity check 2: the identity matrix `I₂` is an isometry. -/
example : IsIsometry (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  simp [IsIsometry]

/-- Sanity check 3: the `3 × 3` identity matrix satisfies `SatisfiesOverlapCond` with `η = 0`,
while the `2 × 2` all-ones matrix fails `SatisfiesOverlapCond` at `η = 0`. -/
example :
    SatisfiesOverlapCond (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 ∧
      ¬ SatisfiesOverlapCond (Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ)) 0 := by
  refine ⟨?_, ?_⟩
  · unfold SatisfiesOverlapCond overlapPairCount
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
  · unfold SatisfiesOverlapCond overlapPairCount
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

/-- Sanity check 4 (Definition 2.1): `(1/√2, 1/√2) ∈ ℝ²` is `(1, 1/2)`-flat, whereas `(1, 0) ∈ ℝ²`
is `(1, 1/2)`-spiky. -/
example :
    IsFlatVec 1 (1 / 2) (![1 / Real.sqrt 2, 1 / Real.sqrt 2]) ∧
      IsSpikyVec 1 (1 / 2) (![(1 : ℝ), 0]) := by
  have : Nonempty {I : Finset (Fin 2) // I.card ≤ 1} := ⟨⟨∅, Nat.zero_le _⟩⟩
  refine ⟨?_, ?_⟩
  · unfold IsFlatVec distSparse distSparseSq
    rw [Real.le_sqrt (by norm_num) (le_ciInf fun I => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine le_ciInf ?_
    rintro ⟨I, hI⟩
    have hnotall : ∃ j : Fin 2, j ∉ I := by
      by_contra hall
      push Not at hall
      have hcard : I.card = 2 := by
        have hIU : I = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
        rw [hIU]
        decide
      omega
    obtain ⟨j, hj⟩ := hnotall
    have hjc : j ∈ Iᶜ := Finset.mem_compl.mpr hj
    have hsingle : (![1 / Real.sqrt 2, 1 / Real.sqrt 2] j) ^ 2 ≤
        ∑ i ∈ Iᶜ, (![1 / Real.sqrt 2, 1 / Real.sqrt 2] i) ^ 2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) hjc
    have hval : (![1 / Real.sqrt 2, 1 / Real.sqrt 2] j) ^ 2 = 1 / 2 := by
      fin_cases j <;> simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  · unfold IsSpikyVec distSparse distSparseSq
    have hle : (⨅ I : {I : Finset (Fin 2) // I.card ≤ 1}, ∑ i ∈ (I.1)ᶜ, (![(1 : ℝ), 0] i) ^ 2) ≤ 0 := by
      refine ciInf_le_of_le ⟨(0 : ℝ), ?_⟩ ⟨{(0 : Fin 2)}, by decide⟩ ?_
      · rintro _ ⟨I, rfl⟩
        exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      · have hc : ({(0 : Fin 2)} : Finset (Fin 2))ᶜ = {(1 : Fin 2)} := by decide
        rw [hc]
        simp
    have hge : 0 ≤ ⨅ I : {I : Finset (Fin 2) // I.card ≤ 1}, ∑ i ∈ (I.1)ᶜ, (![(1 : ℝ), 0] i) ^ 2 :=
      le_ciInf fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have heq : (⨅ I : {I : Finset (Fin 2) // I.card ≤ 1}, ∑ i ∈ (I.1)ᶜ, (![(1 : ℝ), 0] i) ^ 2) = 0 :=
      le_antisymm hle hge
    rw [heq, Real.sqrt_zero]
    norm_num

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
end OsiUb
