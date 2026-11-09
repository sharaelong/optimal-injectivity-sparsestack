import SparseStack.Cross.MatrixNorm
import SparseStack.Cross.ProbLemmas
import SparseStack.Bridge.FiniteLawAux

/-!
# Cross-Gram bound, step (3): distributional identity and restoring entries (W-CROSS)

For fixed `t`, distinct unique-head coordinates `i` occupy distinct buckets `h⁰_t(i)`
(`headCoef_inj`), so the variables `σ⁰_{ti} y_{tj}(h⁰_t(i))` (`headCoef t i ≠ 0`) are independent
ternary variables. Completing them by fresh independent ternary variables for the entries with
`α_{ti} = 0` (`restoreSample`) gives an iid family (`expect_restoreSample`, selection identity),
and the completed aggregate matrix `U` has the structured matrix as conditional expectation
(`structMat_yValue_eq_expectMat`), so Jensen gives `E ‖s⁻¹ ∑ A_t y_{tj} v_jᵀ‖ ≤ E ‖U V / s‖`
(paper, eq. (aggregate-comparison)).

Proof (W-HEID): the fresh variables are centered (`expect_aggLaw_yValue`), and a selected
variable is `σ⁰_{ti} y_{tj}(h⁰_t(i))` (`yValue_signAdj`), which gives the conditional
expectation identity entrywise; `expect_restoreSample` is `expect_select_nested` with the
selection `(i,j), t ↦ (t, j), h⁰_t(i)` (injective on the selected entries by `headCoef_inj`) and
the sign flips `signAdj σ⁰_{ti}` (measure-preserving involutions).
-/

namespace SparseStack
namespace Cross

open SparseFock SparseFock.SparseIIDCoupling
open scoped Matrix.Norms.L2Operator

/-- A nonzero head coefficient comes from a head coordinate in a unique-head bucket. -/
theorem headCoef_ne_zero {s b n : ℕ} {I : Finset (Fin n)} {ω₀ : SketchSample s b n} {t : Fin s}
    {i : Fin n} (h : headCoef I ω₀ t i ≠ 0) :
    i ∈ I ∧ bucketLoad I ω₀ t (ω₀.1 t i) = 1 := by
  by_contra hc
  apply h
  unfold headCoef
  rw [if_neg hc]

/-- A nonzero head coefficient is the head sign. -/
theorem headCoef_eq_of_ne_zero {s b n : ℕ} {I : Finset (Fin n)} {ω₀ : SketchSample s b n}
    {t : Fin s} {i : Fin n} (h : headCoef I ω₀ t i ≠ 0) :
    headCoef I ω₀ t i = signValue (ω₀.2 t i) := by
  have hc := headCoef_ne_zero h
  unfold headCoef
  rw [if_pos hc]

/-- Unique-head buckets: in a fixed block, distinct coordinates with nonzero head coefficient
occupy distinct buckets. -/
theorem headCoef_inj {s b n : ℕ} {I : Finset (Fin n)} {ω₀ : SketchSample s b n} {t : Fin s}
    {i i' : Fin n} (h : headCoef I ω₀ t i ≠ 0) (h' : headCoef I ω₀ t i' ≠ 0)
    (hu : ω₀.1 t i = ω₀.1 t i') : i = i' := by
  obtain ⟨hi, hl⟩ := headCoef_ne_zero h
  obtain ⟨hi', _⟩ := headCoef_ne_zero h'
  unfold bucketLoad at hl
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hl
  have h1 : i ∈ I.filter (fun i'' => ω₀.1 t i'' = ω₀.1 t i) := Finset.mem_filter.2 ⟨hi, rfl⟩
  have h2 : i' ∈ I.filter (fun i'' => ω₀.1 t i'' = ω₀.1 t i) :=
    Finset.mem_filter.2 ⟨hi', hu.symm⟩
  rw [ha, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

/-- Sign adjustment of a ternary outcome by a head sign bit. -/
def signAdj (β : Bool) (z : EtaOutcome) : EtaOutcome := if β then z else negateOutcome z

/-- The restored aggregate sample: the entries `(i,j)` with `α_{ti} = 1` read the coupled
coordinate `σ⁰_{ti} y_{tj}(h⁰_t(i))`, the others the fresh variable `x'_{tij}`. -/
noncomputable def restoreSample {s b n : ℕ} (I : Finset (Fin n)) (ω₀ : SketchSample s b n)
    (y : Fin s × Fin n → YVector b) (x' : Fin n × Fin n → Fin s → EtaOutcome) :
    Fin n × Fin n → Fin s → EtaOutcome :=
  fun e t => if headCoef I ω₀ t e.1 ≠ 0 then signAdj (ω₀.2 t e.1) (y (t, e.2) (ω₀.1 t e.1))
    else x' e t

/-- `yValue (signAdj β z) = ±1 · yValue z`. -/
theorem yValue_signAdj (β : Bool) (z : EtaOutcome) :
    yValue (signAdj β z) = signValue β * yValue z := by
  cases β
  · simp only [signAdj, Bool.false_eq_true, if_false, yValue_negateOutcome, signValue]
    ring
  · simp only [signAdj, if_true, signValue]
    ring

/-- `signAdj β` is an involution. -/
theorem signAdj_signAdj (β : Bool) (z : EtaOutcome) : signAdj β (signAdj β z) = z := by
  cases β
  · simp only [signAdj, Bool.false_eq_true, if_false, negateOutcome_involutive]
  · simp only [signAdj, if_true]

/-- `signAdj β` preserves the ternary law. -/
theorem coordinateLaw_weight_signAdj {b : ℕ} (hb : 0 < b) (β : Bool) (z : EtaOutcome) :
    (coordinateLaw b hb).weight (signAdj β z) = (coordinateLaw b hb).weight z := by
  cases β
  · simp only [signAdj, Bool.false_eq_true, if_false, coordinateLaw_weight, mass_negateOutcome]
  · simp only [signAdj, if_true]

/-- The fresh ternary variables are centered. -/
theorem expect_aggLaw_yValue {s b n : ℕ} (hb : 0 < b) (e : Fin n × Fin n) (t : Fin s) :
    (aggLaw s n b hb).expect (fun x' => yValue (x' e t)) = 0 := by
  have h1 : (aggLaw s n b hb).expect (fun x' => yValue (x' e t)) =
      (rowLaw s b hb).expect (fun w => yValue (w t)) :=
    FiniteLaw.expect_independentProduct_apply (fun _ => rowLaw s b hb) e (fun w => yValue (w t))
  have h2 : (rowLaw s b hb).expect (fun w => yValue (w t)) =
      (coordinateLaw b hb).expect yValue :=
    FiniteLaw.expect_independentProduct_apply (fun _ => coordinateLaw b hb) t yValue
  rw [h1, h2]
  simp only [FiniteLaw.expect, coordinateLaw_weight, univ_etaOutcome]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [TernaryJacobi.mass, yValue]
  ring

/-- The structured matrix of the coupled vectors is the conditional expectation (over the fresh
variables) of the restored aggregate matrix. -/
theorem structMat_yValue_eq_expectMat {s b n d : ℕ} (hb : 0 < b) (I : Finset (Fin n))
    (ω₀ : SketchSample s b n) (V : Matrix (Fin n) (Fin d) ℝ) (y : Fin s × Fin n → YVector b) :
    structMat I ω₀ V (fun p u => yValue (y p u)) =
      expectMat (aggLaw s n b hb)
        (fun x' => (s : ℝ)⁻¹ • (fullMat I (restoreSample I ω₀ y x') * V)) := by
  ext i k
  simp only [structMat, expectMat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, fullMat]
  by_cases hi : i ∈ I
  · simp only [if_pos hi, rowSum]
    have hpt : ∀ x' : Fin n × Fin n → Fin s → EtaOutcome,
        (s : ℝ)⁻¹ * ∑ j, (∑ t, yValue (restoreSample I ω₀ y x' (i, j) t)) * V j k =
          ∑ j, ∑ t, ((s : ℝ)⁻¹ * V j k) * yValue (restoreSample I ω₀ y x' (i, j) t) := by
      intro x'
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [FiniteLaw.expect_congr _ hpt, HeidBridge.expect_finset_sum]
    simp_rw [HeidBridge.expect_finset_sum, FiniteLaw.expect_smul]
    have hval : ∀ (j : Fin n) (t : Fin s),
        (aggLaw s n b hb).expect (fun x' => yValue (restoreSample I ω₀ y x' (i, j) t)) =
          headCoef I ω₀ t i * yValue (y (t, j) (ω₀.1 t i)) := by
      intro j t
      by_cases hc : headCoef I ω₀ t i ≠ 0
      · have hconst : ∀ x' : Fin n × Fin n → Fin s → EtaOutcome,
            yValue (restoreSample I ω₀ y x' (i, j) t) =
              yValue (signAdj (ω₀.2 t i) (y (t, j) (ω₀.1 t i))) := by
          intro x'
          simp only [restoreSample, if_pos hc]
        rw [FiniteLaw.expect_congr _ hconst, FiniteLaw.expect_const, yValue_signAdj,
          headCoef_eq_of_ne_zero hc]
      · have hfresh : ∀ x' : Fin n × Fin n → Fin s → EtaOutcome,
            yValue (restoreSample I ω₀ y x' (i, j) t) = yValue (x' (i, j) t) := by
          intro x'
          simp only [restoreSample, if_neg hc]
        rw [FiniteLaw.expect_congr _ hfresh, expect_aggLaw_yValue]
        rw [not_not] at hc
        rw [hc, zero_mul]
    simp_rw [hval]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · have h0 : ∀ t, headCoef I ω₀ t i = 0 := by
      intro t
      unfold headCoef
      rw [if_neg (fun h => hi h.1)]
    simp only [if_neg hi, zero_mul, Finset.sum_const_zero, mul_zero, h0, FiniteLaw.expect_zero]

/-- The restored aggregate sample is an iid family (selection identity). -/
theorem expect_restoreSample {s b n : ℕ} (hb : 0 < b) (I : Finset (Fin n))
    (ω₀ : SketchSample s b n) (F : (Fin n × Fin n → Fin s → EtaOutcome) → ℝ) :
    (coupledLaw s n b hb).expect (fun y =>
      (aggLaw s n b hb).expect (fun x' => F (restoreSample I ω₀ y x'))) =
      (aggLaw s n b hb).expect F := by
  have hφ : ∀ (e₁ : Fin n × Fin n) (e₂ : Fin s) (e₁' : Fin n × Fin n) (e₂' : Fin s),
      headCoef I ω₀ e₂ e₁.1 ≠ 0 → headCoef I ω₀ e₂' e₁'.1 ≠ 0 →
      (e₂, e₁.2) = (e₂', e₁'.2) → ω₀.1 e₂ e₁.1 = ω₀.1 e₂' e₁'.1 → e₁ = e₁' ∧ e₂ = e₂' := by
    intro e₁ e₂ e₁' e₂' h h' h12 hu
    obtain ⟨ht, hj⟩ := Prod.mk.inj h12
    subst ht
    exact ⟨Prod.ext (headCoef_inj h h' hu) hj, rfl⟩
  have key := expect_select_nested (K₁ := Fin s × Fin n) (K₂ := Fin b) (E₁ := Fin n × Fin n)
    (E₂ := Fin s) (α := EtaOutcome) (coordinateLaw b hb)
    (fun (e₁ : Fin n × Fin n) (e₂ : Fin s) => headCoef I ω₀ e₂ e₁.1 ≠ 0)
    (fun (e₁ : Fin n × Fin n) (e₂ : Fin s) => (e₂, e₁.2))
    (fun (e₁ : Fin n × Fin n) (e₂ : Fin s) => ω₀.1 e₂ e₁.1) hφ
    (fun (e₁ : Fin n × Fin n) (e₂ : Fin s) => signAdj (ω₀.2 e₂ e₁.1))
    (fun _ _ a => signAdj_signAdj _ a) (fun _ _ a => coordinateLaw_weight_signAdj hb _ a) F
  exact key

/-- **Step (3)** (paper, eq. (aggregate-comparison)). -/
theorem restore_bound {s b n d : ℕ} (hb : 0 < b) (I : Finset (Fin n)) (ω₀ : SketchSample s b n)
    (V : Matrix (Fin n) (Fin d) ℝ) :
    (coupledLaw s n b hb).expect (fun y => ‖structMat I ω₀ V (fun p u => yValue (y p u))‖) ≤
      (aggLaw s n b hb).expect (fun x => ‖(s : ℝ)⁻¹ • (fullMat I x * V)‖) := by
  calc (coupledLaw s n b hb).expect (fun y => ‖structMat I ω₀ V (fun p u => yValue (y p u))‖)
      = (coupledLaw s n b hb).expect (fun y => ‖expectMat (aggLaw s n b hb)
          (fun x' => (s : ℝ)⁻¹ • (fullMat I (restoreSample I ω₀ y x') * V))‖) := by
        apply FiniteLaw.expect_congr
        intro y
        rw [structMat_yValue_eq_expectMat hb I ω₀ V y]
    _ ≤ (coupledLaw s n b hb).expect (fun y => (aggLaw s n b hb).expect
          (fun x' => ‖(s : ℝ)⁻¹ • (fullMat I (restoreSample I ω₀ y x') * V)‖)) := by
        apply FiniteLaw.expect_mono
        intro y
        exact norm_expectMat_le _ _
    _ = (aggLaw s n b hb).expect (fun x => ‖(s : ℝ)⁻¹ • (fullMat I x * V)‖) :=
        expect_restoreSample hb I ω₀ (fun x => ‖(s : ℝ)⁻¹ • (fullMat I x * V)‖)

end Cross
end SparseStack
