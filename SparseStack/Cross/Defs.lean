import SparseStack.Prob.Sketch
import SparseStack.Prob.Resample
import SparseFockFormal.SparseIIDCoupling
import SparseFockFormal.ProductFock

/-!
# Refined cross-Gram bound: shared definitions (W-CROSS)

Objects used along the proof of `cross_gram_refined` (paper, lines 631–775 and 800–869).

* `expectMat μ M`: entrywise expectation of a matrix-valued function.
* `toRaw ω`: the sketch sample as Heidary's raw selector sample (`(hash, sign)` per `(t, j)`).
* `selVec x u = σ [u = h]`: the signed coordinate vector `ξ = σ e_h ∈ ℝ^b` of a selector.
* `headCoef I ω₀ t i = σ⁰_{ti}` if `i ∈ I` occupies a unique-head bucket of block `t`, else `0`
  (`α_{ti} σ_{ti}` of the paper).
* `structMat I ω₀ V ζ = s⁻¹ ∑_{t,j} A_t ζ_{tj} v_jᵀ`, entry `(i,k)`:
  `s⁻¹ ∑_t headCoef t i ∑_j ζ_{tj}(h⁰_t(i)) V_{jk}` (step (1)).
* `coupledLaw`: independent iid ternary vectors `y_{tj} ∈ {-1,0,1}^b` (step (2)).
* `rowLaw`, `aggLaw`: independent ternary variables `x_{tij}` (parameter `b`), grouped by entry
  `(i,j)` (step (3)); `rowSum`, `nzCount`, `loPart`, `hiPart`; `fullMat = U`, `loMat = U^lo`,
  `hiMat = U^hi` (rows outside `I` are zero) (step (4)).
* `ternLaw`, `ternMat`: the iid ternary comparison matrix `X` with parameter `B`, rows outside `I`
  zero (step (5)); `iidMat`: Heidary's `m × n` iid ternary matrix (= `iidMatrix`) (steps (6)–(7)).
-/

namespace SparseStack
namespace Cross

open SparseFock SparseFock.SparseIIDCoupling SparseFock.SparseStackDistribution
  SparseFock.SparseStackModel

noncomputable section

/-! ## Matrix-valued expectation -/

/-- Entrywise expectation of a matrix-valued function under a finite law. -/
def expectMat {α : Type*} [Fintype α] {m l : Type*} (μ : FiniteLaw α)
    (M : α → Matrix m l ℝ) : Matrix m l ℝ :=
  Matrix.of fun i k => μ.expect (fun x => M x i k)

/-! ## The sketch as a raw selector sample -/

/-- Heidary's sign of a sign bit (`true ↦ +1`, `false ↦ -1`). -/
def boolToSign : Bool → Sign
  | true => .plus
  | false => .minus

/-- The raw selector sample (Heidary's `RawSample`) of a sketch sample:
`(t, j) ↦ (h_t(j), σ_{tj})`. -/
def toRaw {s b n : ℕ} (ω : SketchSample s b n) : RawSample s b n :=
  fun p => (ω.1 p.1 p.2, boolToSign (ω.2 p.1 p.2))

/-- The signed coordinate vector `σ e_h ∈ ℝ^b` of a selector `x = (h, σ)`. -/
def selVec {b : ℕ} (x : SignedHash b) (u : Fin b) : ℝ := if u = x.1 then x.2.val else 0

/-! ## Structure of the cross-Gram matrix for a fixed head -/

/-- `α_{ti} σ⁰_{ti}`: the head sign if `i ∈ I` occupies a unique-head bucket in block `t`. -/
def headCoef {s b n : ℕ} (I : Finset (Fin n)) (ω₀ : SketchSample s b n) (t : Fin s)
    (i : Fin n) : ℝ :=
  if i ∈ I ∧ bucketLoad I ω₀ t (ω₀.1 t i) = 1 then signValue (ω₀.2 t i) else 0

/-- The structured matrix `s⁻¹ ∑_{t,j} A_t ζ_{tj} v_jᵀ` (rows indexed by all coordinates, zero
outside `I`), for a family `ζ_{tj} ∈ ℝ^b` indexed by `(t, j)`. -/
def structMat {s b n d : ℕ} (I : Finset (Fin n)) (ω₀ : SketchSample s b n)
    (V : Matrix (Fin n) (Fin d) ℝ) (ζ : Fin s × Fin n → Fin b → ℝ) : Matrix (Fin n) (Fin d) ℝ :=
  Matrix.of fun i k => (s : ℝ)⁻¹ * ∑ t, headCoef I ω₀ t i * ∑ j, ζ (t, j) (ω₀.1 t i) * V j k

/-- Independent iid ternary vectors `y_{tj} ∈ {-1,0,1}^b`, one for every `(t, j)`. -/
def coupledLaw (s n b : ℕ) (hb : 0 < b) : FiniteLaw (Fin s × Fin n → YVector b) :=
  FiniteLaw.independentProduct (fun _ : Fin s × Fin n => yVectorLaw b hb)

/-! ## The aggregate comparison matrix `U` and its multiplicity split -/

/-- `s` independent ternary variables with parameter `b` (one entry `(x_{tij})_t` of `U`). -/
def rowLaw (s b : ℕ) (hb : 0 < b) : FiniteLaw (Fin s → EtaOutcome) :=
  FiniteLaw.independentProduct (fun _ : Fin s => coordinateLaw b hb)

/-- All variables `x_{tij}`, grouped by the entry `(i, j)`. -/
def aggLaw (s n b : ℕ) (hb : 0 < b) : FiniteLaw (Fin n × Fin n → Fin s → EtaOutcome) :=
  FiniteLaw.independentProduct (fun _ : Fin n × Fin n => rowLaw s b hb)

/-- Multiplicity `c = #{t : x_t ≠ 0}`. -/
def nzCount {s : ℕ} (w : Fin s → EtaOutcome) : ℕ :=
  (Finset.univ.filter (fun t => w t ≠ EtaOutcome.zero)).card

/-- `U_{ij} = ∑_t x_{tij}`. -/
def rowSum {s : ℕ} (w : Fin s → EtaOutcome) : ℝ := ∑ t, yValue (w t)

/-- Low-multiplicity part `U_{ij} 1{c_{ij} ≤ 2}`. -/
def loPart {s : ℕ} (w : Fin s → EtaOutcome) : ℝ := if nzCount w ≤ 2 then rowSum w else 0

/-- High-multiplicity part `U_{ij} 1{c_{ij} ≥ 3}`. -/
def hiPart {s : ℕ} (w : Fin s → EtaOutcome) : ℝ := if nzCount w ≤ 2 then 0 else rowSum w

/-- The aggregate matrix `U` (rows outside `I` are zero). -/
def fullMat {s n : ℕ} (I : Finset (Fin n)) (x : Fin n × Fin n → Fin s → EtaOutcome) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i ∈ I then rowSum (x (i, j)) else 0

/-- `U^lo`. -/
def loMat {s n : ℕ} (I : Finset (Fin n)) (x : Fin n × Fin n → Fin s → EtaOutcome) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i ∈ I then loPart (x (i, j)) else 0

/-- `U^hi`. -/
def hiMat {s n : ℕ} (I : Finset (Fin n)) (x : Fin n × Fin n → Fin s → EtaOutcome) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i ∈ I then hiPart (x (i, j)) else 0

/-! ## The iid ternary comparison matrices -/

/-- Independent ternary variables with parameter `B`, one for every entry `(i, j)`. -/
def ternLaw (n B : ℕ) (hB : 0 < B) : FiniteLaw (Fin n × Fin n → EtaOutcome) :=
  FiniteLaw.independentProduct (fun _ : Fin n × Fin n => TernaryJacobi.law B hB)

/-- The iid ternary matrix `X_N` with entries in `{-1,0,1}` (rows outside `I` are zero). -/
def ternMat {n : ℕ} (B : ℕ) (I : Finset (Fin n)) (z : Fin n × Fin n → EtaOutcome) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i ∈ I then TernaryJacobi.eta B (z (i, j)) / Real.sqrt B else 0

/-- Heidary's iid ternary matrix `X_{ℓj} = η_{ℓj}/√B` (definitionally `iidMatrix`). -/
def iidMat {m n : ℕ} (B : ℕ) (x : ProductFock.Configuration m n) : Matrix (Fin m) (Fin n) ℝ :=
  fun ℓ j => TernaryJacobi.eta B (x (ℓ, j)) / Real.sqrt B

end

end Cross
end SparseStack
