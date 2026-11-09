import SparseStack.Cross.MatrixNorm
import SparseStack.Cross.ProbLemmas
import SparseStack.Bridge.FiniteLawAux

/-!
# Cross-Gram bound, step (2): selector coupling and conditional Jensen (W-CROSS)

Heidary's exact coupling (`SparseIIDCoupling`): `y ~ yVectorLaw b` (iid ternary vector), and
given `y` a selector `x`; then `x ~ selectorLaw b` and `E[c_b y | x] = selVec x`
(`conditional_barycenter_coordinate`). Applied independently to all background selectors, the
structured matrix is a conditional expectation of `c_b` times the same matrix built from `y`, so
`E ‖H̃ᵀỸ‖ ≤ c_b E ‖s⁻¹ ∑ A_t y_{tj} v_jᵀ‖` (paper, eq. (13)).

Proof (W-HEID):
* `selector_conditional_marginal`: Bayes, `∑ₓ P(x) P(y | x) = ∑ₓ P(y, x) = P(y)` (the selection
  kernel `X | Y = y` is normalized);
* `expectMat_smul_structMat`: `structMat` is linear in the family `ζ`, so a matrix expectation of
  `c • structMat(ζ)` is `structMat` of the coordinatewise expectations of `c ζ`;
* `structMat_selVec_eq_expectMat`: under `∏_{(t,j)} P(· | x_{tj})` the coordinate `y_{tj}` has
  law `P(· | x_{tj})`, whose `c_b`-barycenter is `selVec x_{tj}` (Heidary);
* `coupling_bound`: conditional Jensen `‖E M‖ ≤ E ‖M‖` (`norm_expectMat_le`) and the mixture
  identity (`expect_mixture`): drawing the selectors `x ~ rawSampleLaw` and then
  `y ~ ∏ P(· | x_{tj})` gives `y ~ coupledLaw`.
-/

namespace SparseStack
namespace Cross

open SparseFock SparseFock.SparseIIDCoupling SparseFock.SparseStackDistribution
  SparseFock.SparseStackModel
open scoped Matrix.Norms.L2Operator

/-- The selector marginal of Heidary's conditional law is the iid ternary law. -/
theorem selector_conditional_marginal {b : ℕ} (hb : 0 < b) (y : YVector b) :
    ∑ x, (selectorLaw b hb).weight x * (conditionalYLaw hb x).weight y =
      (yVectorLaw b hb).weight y := by
  have h : ∀ x, (selectorLaw b hb).weight x * (conditionalYLaw hb x).weight y =
      (yVectorLaw b hb).weight y * kernelWeight hb y x := by
    intro x
    rw [conditionalYLaw_weight, jointColumnLaw_weight]
    field_simp [ne_of_gt (selectorWeight_pos hb x)]
  simp_rw [h]
  rw [← Finset.mul_sum, sum_kernelWeight hb y, mul_one]

/-- `structMat` is linear in the family `ζ`: the matrix expectation of `c • structMat(ζ)` is
`structMat` of the coordinatewise expectations of `c ζ`. -/
theorem expectMat_smul_structMat {α : Type*} [Fintype α] {s b n d : ℕ} (μ : FiniteLaw α)
    (c : ℝ) (I : Finset (Fin n)) (ω₀ : SketchSample s b n) (V : Matrix (Fin n) (Fin d) ℝ)
    (ζ : α → Fin s × Fin n → Fin b → ℝ) :
    expectMat μ (fun y => c • structMat I ω₀ V (ζ y)) =
      structMat I ω₀ V (fun p u => μ.expect (fun y => c * ζ y p u)) := by
  ext i k
  simp only [expectMat, structMat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have hpt : ∀ y, c * ((s : ℝ)⁻¹ * ∑ t, headCoef I ω₀ t i * ∑ j, ζ y (t, j) (ω₀.1 t i) * V j k) =
      ∑ t, ∑ j, ((s : ℝ)⁻¹ * headCoef I ω₀ t i * V j k) * (c * ζ y (t, j) (ω₀.1 t i)) := by
    intro y
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [FiniteLaw.expect_congr μ hpt, HeidBridge.expect_finset_sum]
  simp_rw [HeidBridge.expect_finset_sum, FiniteLaw.expect_smul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The structured matrix of the selectors is the conditional expectation of `c_b` times the
structured matrix of the coupled ternary vectors. -/
theorem structMat_selVec_eq_expectMat {s b n d : ℕ} (hb : 0 < b) (I : Finset (Fin n))
    (ω₀ : SketchSample s b n) (V : Matrix (Fin n) (Fin d) ℝ) (z : RawSample s b n) :
    structMat I ω₀ V (fun p => selVec (z p)) =
      expectMat (FiniteLaw.independentProduct (fun p => conditionalYLaw hb (z p)))
        (fun y => cB b • structMat I ω₀ V (fun p u => yValue (y p u))) := by
  rw [expectMat_smul_structMat]
  congr 1
  funext p u
  have h1 : (FiniteLaw.independentProduct (fun p => conditionalYLaw hb (z p))).expect
      (fun y => cB b * yValue (y p u)) =
      (conditionalYLaw hb (z p)).expect (fun y' => cB b * yValue (y' u)) :=
    FiniteLaw.expect_independentProduct_apply (fun p => conditionalYLaw hb (z p)) p
      (fun y' => cB b * yValue (y' u))
  rw [h1, conditional_barycenter_coordinate hb (z p) u]
  rfl

/-- **Step (2)** (paper, eq. (13)): selector coupling and conditional Jensen.

This is the explicit coupling between the spec's uniform selector law (`rawSampleLaw`, the push
forward of the uniform `sketchLaw`, see `expect_sketchLaw_toRaw`) and the iid ternary law
(`coupledLaw`): for every fixed head `ω₀`,
`E_{z ~ rawSampleLaw} ‖structMat(selVec ∘ z)‖ ≤ c_b · E_{y ~ coupledLaw} ‖structMat(yValue ∘ y)‖`.
It combines Heidary's exact one-column coupling (`SparseIIDCoupling`: `x ~ selectorLaw`,
`y | x ~ conditionalYLaw`, `y ~ yVectorLaw`, `E[c_b y | x] = selVec x`), applied independently to
every `(t, j)`, with conditional Jensen for the operator norm. -/
theorem coupling_bound {s b n d : ℕ} (hb : 0 < b) (I : Finset (Fin n)) (ω₀ : SketchSample s b n)
    (V : Matrix (Fin n) (Fin d) ℝ) :
    (rawSampleLaw s b n hb).expect (fun z => ‖structMat I ω₀ V (fun p => selVec (z p))‖) ≤
      cB b * (coupledLaw s n b hb).expect
        (fun y => ‖structMat I ω₀ V (fun p u => yValue (y p u))‖) := by
  have hcB : 0 ≤ cB b := zero_le_one.trans (one_le_cB hb)
  calc (rawSampleLaw s b n hb).expect (fun z => ‖structMat I ω₀ V (fun p => selVec (z p))‖)
      = (rawSampleLaw s b n hb).expect (fun z =>
          ‖expectMat (FiniteLaw.independentProduct (fun p => conditionalYLaw hb (z p)))
            (fun y => cB b • structMat I ω₀ V (fun p u => yValue (y p u)))‖) := by
        apply FiniteLaw.expect_congr
        intro z
        rw [structMat_selVec_eq_expectMat hb I ω₀ V z]
    _ ≤ (rawSampleLaw s b n hb).expect (fun z =>
          (FiniteLaw.independentProduct (fun p => conditionalYLaw hb (z p))).expect
            (fun y => ‖cB b • structMat I ω₀ V (fun p u => yValue (y p u))‖)) := by
        apply FiniteLaw.expect_mono
        intro z
        exact norm_expectMat_le _ _
    _ = (rawSampleLaw s b n hb).expect (fun z =>
          (FiniteLaw.independentProduct (fun p => conditionalYLaw hb (z p))).expect
            (fun y => cB b * ‖structMat I ω₀ V (fun p u => yValue (y p u))‖)) := by
        apply FiniteLaw.expect_congr
        intro z
        apply FiniteLaw.expect_congr
        intro y
        rw [norm_smul, Real.norm_of_nonneg hcB]
    _ = cB b * (rawSampleLaw s b n hb).expect (fun z =>
          (FiniteLaw.independentProduct (fun p => conditionalYLaw hb (z p))).expect
            (fun y => ‖structMat I ω₀ V (fun p u => yValue (y p u))‖)) := by
        simp_rw [FiniteLaw.expect_smul]
    _ = cB b * (coupledLaw s n b hb).expect
          (fun y => ‖structMat I ω₀ V (fun p u => yValue (y p u))‖) := by
        congr 1
        exact expect_mixture (selectorLaw b hb) (yVectorLaw b hb) (conditionalYLaw hb)
          (selector_conditional_marginal hb) _

end Cross
end SparseStack
