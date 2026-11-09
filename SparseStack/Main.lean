import SparseStack.CaseA
import SparseStack.CaseB
import SparseStack.SpecSanity

/-!
# Main theorem (paper, proof of `thm:main`, lines 1340–1387)

Both headlines of `SparseStack/Spec.lean` are proved here; their types are literally the Spec
definitions `SparseStack.MainTheorem` and `SparseStack.ConstantInjectionQuadratic`.
-/

namespace SparseStack

/-- `thm:main`, probability clause, Rayleigh form: Case A or Case B of method D. -/
theorem constantInjectionQuadratic_proof : ConstantInjectionQuadratic := by
  intro n r hr hrn Q hQ
  by_cases h : logER r < 64 ∨ 104 * logER r ≤ (numBlocks r : ℝ)
  · exact caseA hr hrn Q hQ h
  · push Not at h
    exact caseB hr hrn Q hQ h.1 h.2

/-- `thm:main`, probability clause, eigenvalue form. -/
theorem constantInjection_proof : ConstantInjection :=
  constantInjection_iff_quadratic.2 constantInjectionQuadratic_proof

/-- `thm:main`, `E Ω Ωᵀ = I_n`. -/
theorem meanIdentity_proof : MeanIdentity := by
  intro n r hr _
  have hs : 0 < numBlocks r := lt_of_lt_of_le (by norm_num) (numBlocks_ge_2000 hr)
  have hb : 0 < numBuckets r := lt_of_lt_of_le (by norm_num) (two_le_numBuckets hr)
  exact meanIdentity_all hs hb

/-- `thm:main`, `b ζ ≤ K r + ζ ≤ (K + C + 1) r`. -/
theorem sizeBounds_proof : SizeBounds := fun _ hr => ⟨numBuckets_mul_le hr, size_le hr⟩

/-- `thm:main`, `α > 10⁻⁴`. -/
theorem alphaBound_proof : AlphaBound := alpha_gt

/-- **Headline 1**: `thm:main` in full. -/
theorem mainTheorem : MainTheorem :=
  ⟨constantInjection_proof, meanIdentity_proof, sizeBounds_proof, alphaBound_proof⟩

/-- **Headline 2**: the probability clause in Rayleigh form. -/
theorem constantInjectionQuadratic : ConstantInjectionQuadratic :=
  constantInjectionQuadratic_proof

/-- The full theorem with the probability clause in Rayleigh form:
`ConstantInjectionQuadratic ∧ MeanIdentity ∧ SizeBounds ∧ AlphaBound`. Not a Spec headline; a
proved corollary for readers who prefer the quadratic-form statement. -/
theorem mainTheoremQuadratic :
    ConstantInjectionQuadratic ∧ MeanIdentity ∧ SizeBounds ∧ AlphaBound :=
  ⟨constantInjectionQuadratic_proof, meanIdentity_proof, sizeBounds_proof, alphaBound_proof⟩

end SparseStack
