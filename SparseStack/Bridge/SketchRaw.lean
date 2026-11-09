import SparseFockFormal.MatrixFrameBridge
import SparseStack.Prob.Sketch

/-!
# Our SparseStack sample space is Heidary's raw selector sample (eq. (stack-moment) bridge)

* `sketchRawEquiv s b n : SketchSample s b n ≃ RawSample s b n`, coordinatewise
  `(h, σ) ↦ ((t,i) ↦ (h t i, sign of σ t i))` (`true ↦ plus`, `false ↦ minus`);
* `stackMatrix_toSample_sketchRawEquiv`: Heidary's `stackMatrix` of the image is literally our
  `sketchMatrix` (same `s^{-1/2}` row normalization, same `±1` signs, bucket test
  `u = h t i` vs `h t i = u`);
* `sketch_gram_sub_one_eq`: `(Π U)ᵀ(Π U) - I = gramError (frameOfMatrix U hU) (toSample ·)`;
* `expect_sketchLaw_eq_rawSampleLaw`: the uniform `sketchLaw` is the push-back of Heidary's
  `rawSampleLaw` (both laws are uniform).
-/

namespace SparseStack.HeidBridge

open SparseFock SparseStackModel SparseStackDistribution

/-- Sign bit to Heidary's sign: `true ↦ plus`, `false ↦ minus`. -/
def boolToSign : Bool → Sign
  | true => .plus
  | false => .minus

/-- Heidary's sign to a sign bit. -/
def signToBool : Sign → Bool
  | .plus => true
  | .minus => false

theorem signToBool_boolToSign (β : Bool) : signToBool (boolToSign β) = β := by
  cases β <;> rfl

theorem boolToSign_signToBool (e : Sign) : boolToSign (signToBool e) = e := by
  cases e <;> rfl

theorem val_boolToSign (β : Bool) : (boolToSign β).val = signValue β := by
  cases β <;> rfl

/-- Our sample space is Heidary's raw selector sample, coordinate by coordinate. -/
def sketchRawEquiv (s b n : ℕ) : SketchSample s b n ≃ RawSample s b n where
  toFun ω := fun p => (ω.1 p.1 p.2, boolToSign (ω.2 p.1 p.2))
  invFun z := (fun t i => (z (t, i)).1, fun t i => signToBool (z (t, i)).2)
  left_inv ω := by
    rcases ω with ⟨h, σ⟩
    refine Prod.ext rfl ?_
    funext t i
    exact signToBool_boolToSign (σ t i)
  right_inv z := by
    funext p
    rcases p with ⟨t, i⟩
    change ((z (t, i)).1, boolToSign (signToBool (z (t, i)).2)) = z (t, i)
    rw [boolToSign_signToBool]

@[simp] theorem sketchRawEquiv_apply {s b n : ℕ} (ω : SketchSample s b n) (t : Fin s) (i : Fin n) :
    sketchRawEquiv s b n ω (t, i) = (ω.1 t i, boolToSign (ω.2 t i)) := rfl

/-- Heidary's stacked matrix of the image sample is our sketch matrix. -/
theorem stackMatrix_toSample_sketchRawEquiv {s b n : ℕ} (ω : SketchSample s b n) :
    stackMatrix (toSample (sketchRawEquiv s b n ω)) = sketchMatrix ω := by
  ext ⟨t, u⟩ i
  rw [stackMatrix_apply, toSample_hash, toSample_sign, sketchRawEquiv_apply]
  simp only [sketchMatrix, invSqrt]
  rw [val_boolToSign]
  by_cases h : ω.1 t i = u
  · rw [if_pos h.symm, if_pos h]
  · have h' : ¬ u = ω.1 t i := fun h'' => h h''.symm
    rw [if_neg h', if_neg h]

/-- `(Π U)ᵀ(Π U) - I` is Heidary's Gram error of the frame of `U` at the image sample. -/
theorem sketch_gram_sub_one_eq {s b n D : ℕ} (U : Matrix (Fin n) (Fin D) ℝ)
    (hU : U.transpose * U = 1) (ω : SketchSample s b n) :
    (sketchMatrix ω * U).transpose * (sketchMatrix ω * U) - 1 =
      gramError (MatrixFrameBridge.frameOfMatrix U hU) (toSample (sketchRawEquiv s b n ω)) := by
  rw [MatrixFrameBridge.gramError_frameOfMatrix, sketchGram,
    stackMatrix_toSample_sketchRawEquiv, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Heidary's raw law has constant weight. -/
theorem rawSampleLaw_weight {s b n : ℕ} (hb : 0 < b) (z : RawSample s b n) :
    (rawSampleLaw s b n hb).weight z = ∏ _p : Fin s × Fin n, (1 / (2 * (b : ℝ))) := rfl

/-- The uniform sketch law is the push-back of Heidary's raw law along `sketchRawEquiv`. -/
theorem expect_sketchLaw_eq_rawSampleLaw {s b n : ℕ} (hb : 0 < b) (g : RawSample s b n → ℝ) :
    (sketchLaw s b n hb).expect (fun ω => g (sketchRawEquiv s b n ω)) =
      (rawSampleLaw s b n hb).expect g := by
  set c : ℝ := ∏ _p : Fin s × Fin n, (1 / (2 * (b : ℝ))) with hc
  have hsum : (Fintype.card (RawSample s b n) : ℝ) * c = 1 := by
    have h := (rawSampleLaw s b n hb).sum_weight
    simp only [rawSampleLaw_weight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    exact h
  have hcard : Fintype.card (SketchSample s b n) = Fintype.card (RawSample s b n) :=
    Fintype.card_congr (sketchRawEquiv s b n)
  have hcardne : (Fintype.card (RawSample s b n) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hsum
    exact zero_ne_one hsum
  have hw : 1 / (Fintype.card (SketchSample s b n) : ℝ) = c := by
    rw [hcard]
    field_simp
    linarith [hsum]
  simp only [FiniteLaw.expect, rawSampleLaw_weight]
  change ∑ ω, 1 / (Fintype.card (SketchSample s b n) : ℝ) * g (sketchRawEquiv s b n ω) =
    ∑ z, c * g z
  rw [hw]
  exact Equiv.sum_comp (sketchRawEquiv s b n) (fun z => c * g z)

end SparseStack.HeidBridge
