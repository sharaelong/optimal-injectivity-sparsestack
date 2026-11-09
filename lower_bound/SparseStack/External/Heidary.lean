import SparseFockFormal.ConcreteBandEnvelope
import SparseFockFormal.ConcreteLadderIteration

/-!
# External input 1: Heidary, Theorem 7.1, eq. (83) (verified Lean, unchanged)

The paper's eq. (external-moment) is Heidary's Theorem 7.1, first bound of eq. (83), for every
moment order `q ≥ 1`, every `s ≥ 1`, `b ≥ 2` and every Parseval frame:
`E tr(E_iid^{2q}) ≤ d (3 β_q)^{2q}` with
`β_q = (3 + √2)(√(D_q/m) + D_q/m + (2q+1)/s)`, `D_q = d + 2q + 1`, `m = s b`.

It is obtained as a composition of two declarations of Heidary's verified library
`SparseFockFormal` (vendored unchanged at commit `b9da2b5d96e5`), with no new mathematics.
-/

namespace SparseStack.External

open SparseFock ParsevalFrame PaperParameters

/-- Heidary, Theorem 7.1, first bound of eq. (83), for every moment order `q`. -/
theorem heidary_eq83_all_q {n d s b q : ℕ} (hs : 0 < s) (hb : 1 < b) (F : Frame n d) :
    (ProductFock.iidLaw b hb (s * b) n).expect
        (fun omega ↦ Matrix.trace ((VacuumMoment.iidGramError b F omega) ^ (2 * q))) ≤
      (d : ℝ) * (3 * betaEnvelope d q (((s * b : ℕ) : ℝ)) (s : ℝ)) ^ (2 * q) := by
  have hm : (0 : ℝ) < ((s * b : ℕ) : ℝ) := by
    have : 0 < s * b := Nat.mul_pos hs (by omega)
    exact_mod_cast this
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  exact ConcreteLadderIteration.iid_trace_moment_le_of_band_bounds (m := s * b) hb F
    (betaEnvelope_nonneg hm hsR)
    (fun delta nu hnu ↦
      ConcreteBandEnvelope.concrete_band_bound_le_beta F s b q nu hs hb hnu delta)

/-- The envelope constant, unfolded (definitional). -/
theorem betaEnvelope_eq (d q : ℕ) (m s : ℝ) :
    betaEnvelope d q m s = (3 + Real.sqrt 2) *
      (Real.sqrt (((d + 2 * q + 1 : ℕ) : ℝ) / m) + ((d + 2 * q + 1 : ℕ) : ℝ) / m +
        ((2 * q + 1 : ℕ) : ℝ) / s) := by
  rfl

/-- The entry law: `η = ±√b` with probability `1/(2b)` each, `0` otherwise (definitional). -/
theorem eta_law_facts (b : ℕ) :
    TernaryJacobi.eta b .pos = Real.sqrt b ∧ TernaryJacobi.eta b .neg = -Real.sqrt b ∧
      TernaryJacobi.mass b .pos = 1 / (2 * (b : ℝ)) ∧ TernaryJacobi.mass b .zero = 1 - 1 / (b : ℝ) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The Gram error is the hollow sum `(1/m) ∑_r ∑_i ∑_{j ≠ i} η_ri η_rj u_i u_jᵀ` (definitional). -/
theorem iidGramError_eq {m n d : ℕ} (b : ℕ) (F : Frame n d)
    (omega : ProductFock.Configuration m n) :
    VacuumMoment.iidGramError b F omega = (1 / (m : ℝ)) •
      ∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i,
        (ProductFock.etaCoordinate b (r, i) omega * ProductFock.etaCoordinate b (r, j) omega) •
          ParsevalFrame.outer (F.u i) (F.u j) := rfl

end SparseStack.External
