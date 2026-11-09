import SparseStack.Cross.ProbLemmas
import SparseStack.Bridge.SketchRaw

/-!
# Cross-Gram bound, step (1): structure of the cross-Gram matrix for a fixed head (W-CROSS)

For a fixed head `ω₀` (all hashes and signs of the coordinates in `I`) and background `ω`,
`H̃ᵀỸ = s⁻¹ ∑_{t,j} A_t ξ_{tj} v_jᵀ` with `ξ_{tj} = σ_{tj} e_{h_t(j)}` and deterministic `A_t`
(`crossGram_mergeHead_eq`). Rows of `V` in `I` vanish, so the selectors of the head coordinates
do not contribute and `ξ` may be read off `ω` for every `j`.

The uniform law on sketch samples is Heidary's raw selector law (`expect_sketchLaw_toRaw`).

Proof (W-HEID): `crossGram_apply` is the entry formula
`(H̃ᵀỸ)_{ik} = s⁻¹ ∑_t α_{ti}σ_{ti} ∑_j [h_t(j) = h_t(i)] σ_{tj} V_{jk}` (the retained-bucket
indicator is idempotent and the bucket sum collapses at `u = h_t(i)`); the head part of
`mergeHead I ω₀ ω` is that of `ω₀` (`bucketLoad_mergeHead`, `headCoef_mergeHead`), and the
background part is that of `ω` off `I`, where `V` is supported. The law identity is
`HeidBridge.expect_sketchLaw_eq_rawSampleLaw` (`toRaw = HeidBridge.sketchRawEquiv`).
-/

namespace SparseStack
namespace Cross

open SparseFock SparseFock.SparseStackDistribution SparseFock.SparseStackModel

/-- `signValue` is the value of the corresponding Heidary sign. -/
theorem signValue_eq_val (β : Bool) : signValue β = (boolToSign β).val := by
  cases β <;> rfl

/-- The bucket loads of the head coordinates only depend on the head. -/
theorem bucketLoad_mergeHead {s b n : ℕ} (I : Finset (Fin n)) (ω₀ ω : SketchSample s b n)
    (t : Fin s) (u : Fin b) : bucketLoad I (mergeHead I ω₀ ω) t u = bucketLoad I ω₀ t u := by
  have hfilt : I.filter (fun i => (mergeHead I ω₀ ω).1 t i = u) =
      I.filter (fun i => ω₀.1 t i = u) :=
    Finset.filter_congr (fun i hi => by simp only [mergeHead, if_pos hi])
  unfold bucketLoad
  rw [hfilt]

/-- The head coefficients only depend on the head. -/
theorem headCoef_mergeHead {s b n : ℕ} (I : Finset (Fin n)) (ω₀ ω : SketchSample s b n)
    (t : Fin s) (i : Fin n) : headCoef I (mergeHead I ω₀ ω) t i = headCoef I ω₀ t i := by
  by_cases hi : i ∈ I
  · have h1 : (mergeHead I ω₀ ω).1 t i = ω₀.1 t i := by simp only [mergeHead, if_pos hi]
    have h2 : (mergeHead I ω₀ ω).2 t i = ω₀.2 t i := by simp only [mergeHead, if_pos hi]
    unfold headCoef
    rw [bucketLoad_mergeHead, h1, h2]
  · unfold headCoef
    rw [if_neg (fun h => hi h.1), if_neg (fun h => hi h.1)]

/-- Entry formula for the retained cross-Gram matrix:
`(H̃ᵀỸ)_{ik} = s⁻¹ ∑_t α_{ti}σ_{ti} ∑_j [h_t(j) = h_t(i)] σ_{tj} V_{jk}`. -/
theorem crossGram_apply {s b n d : ℕ} (I : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ)
    (ω : SketchSample s b n) (i : Fin n) (k : Fin d) :
    crossGram I V ω i k = (s : ℝ)⁻¹ * ∑ t, headCoef I ω t i *
      ∑ j, (if ω.1 t j = ω.1 t i then signValue (ω.2 t j) else 0) * V j k := by
  set τ : Fin s × Fin b → ℝ := fun p => if bucketLoad I ω p.1 p.2 = 1 then 1 else 0 with hτ
  set ε : Fin n → ℝ := fun i => if i ∈ I then 1 else 0 with hε
  set r : ℝ := (Real.sqrt (s : ℝ))⁻¹ with hr
  have hrr : r * r = (s : ℝ)⁻¹ := by
    rw [hr, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg s)]
  have hL : ∀ p : Fin s × Fin b, (retainMatrix I ω * sketchMatrix ω * coordProj I) p i =
      τ p * sketchMatrix ω p i * ε i := by
    intro p
    rw [retainMatrix, coordProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hR : ∀ p : Fin s × Fin b, (retainMatrix I ω * sketchMatrix ω * V) p k =
      ∑ j, τ p * sketchMatrix ω p j * V j k := by
    intro p
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [retainMatrix, Matrix.diagonal_mul]
  rw [crossGram, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, hL, hR]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_eq_single (ω.1 t i)]
  · -- the surviving bucket `u = h_t(i)`
    have hinner : ∑ j, τ (t, ω.1 t i) * sketchMatrix ω (t, ω.1 t i) j * V j k =
        τ (t, ω.1 t i) * r *
          ∑ j, (if ω.1 t j = ω.1 t i then signValue (ω.2 t j) else 0) * V j k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [sketchMatrix]
      ring
    rw [hinner]
    have hself : sketchMatrix ω (t, ω.1 t i) i = r * signValue (ω.2 t i) := by
      show (Real.sqrt (s : ℝ))⁻¹ *
          (if ω.1 t i = ω.1 t i then signValue (ω.2 t i) else 0) = r * signValue (ω.2 t i)
      rw [if_pos rfl]
    rw [hself]
    set S := ∑ j, (if ω.1 t j = ω.1 t i then signValue (ω.2 t j) else 0) * V j k with hS
    by_cases hi : i ∈ I
    · by_cases hl : bucketLoad I ω t (ω.1 t i) = 1
      · have hc : headCoef I ω t i = signValue (ω.2 t i) := by
          unfold headCoef
          rw [if_pos ⟨hi, hl⟩]
        have hτ1 : τ (t, ω.1 t i) = 1 := by simp only [hτ, if_pos hl]
        have hε1 : ε i = 1 := by simp only [hε, if_pos hi]
        rw [hc, hτ1, hε1]
        linear_combination (signValue (ω.2 t i) * S) * hrr
      · have hc : headCoef I ω t i = 0 := by
          unfold headCoef
          rw [if_neg (fun h => hl h.2)]
        have hτ0 : τ (t, ω.1 t i) = 0 := by simp only [hτ, if_neg hl]
        rw [hc, hτ0]
        ring
    · have hc : headCoef I ω t i = 0 := by
        unfold headCoef
        rw [if_neg (fun h => hi h.1)]
      have hε0 : ε i = 0 := by simp only [hε, if_neg hi]
      rw [hc, hε0]
      ring
  · -- buckets `u ≠ h_t(i)` do not meet column `i`
    intro u _ hu
    have hzero : sketchMatrix ω (t, u) i = 0 := by
      simp only [sketchMatrix]
      rw [if_neg (fun h => hu h.symm), mul_zero]
    rw [hzero]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Step (1).** For a fixed head `ω₀`, the retained cross-Gram matrix is
`s⁻¹ ∑_{t,j} A_t ξ_{tj} v_jᵀ` with the background selectors `ξ_{tj}` of `ω`. -/
theorem crossGram_mergeHead_eq {s b n d : ℕ} (I : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ)
    (hVsupp : ∀ i ∈ I, ∀ k, V i k = 0) (ω₀ ω : SketchSample s b n) :
    crossGram I V (mergeHead I ω₀ ω) = structMat I ω₀ V (fun p => selVec (toRaw ω p)) := by
  ext i k
  rw [crossGram_apply]
  simp only [structMat, Matrix.of_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [headCoef_mergeHead]
  by_cases hc : headCoef I ω₀ t i = 0
  · rw [hc, zero_mul, zero_mul]
  · have hi : i ∈ I := by
      by_contra hi
      apply hc
      unfold headCoef
      rw [if_neg (fun h => hi h.1)]
    have h1 : (mergeHead I ω₀ ω).1 t i = ω₀.1 t i := by simp only [mergeHead, if_pos hi]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ I
    · rw [hVsupp j hj k, mul_zero, mul_zero]
    · have h2 : (mergeHead I ω₀ ω).1 t j = ω.1 t j := by simp only [mergeHead, if_neg hj]
      have h3 : (mergeHead I ω₀ ω).2 t j = ω.2 t j := by simp only [mergeHead, if_neg hj]
      rw [h1, h2, h3]
      show (if ω.1 t j = ω₀.1 t i then signValue (ω.2 t j) else 0) * V j k =
        (if ω₀.1 t i = ω.1 t j then (boolToSign (ω.2 t j)).val else 0) * V j k
      by_cases heq : ω.1 t j = ω₀.1 t i
      · rw [if_pos heq, if_pos heq.symm, signValue_eq_val]
      · rw [if_neg heq, if_neg (Ne.symm heq)]

/-- `toRaw` is the coordinatewise equivalence `HeidBridge.sketchRawEquiv`. -/
theorem toRaw_eq_sketchRawEquiv {s b n : ℕ} (ω : SketchSample s b n) :
    toRaw ω = HeidBridge.sketchRawEquiv s b n ω := by
  funext p
  have h : boolToSign (ω.2 p.1 p.2) = HeidBridge.boolToSign (ω.2 p.1 p.2) := by
    cases ω.2 p.1 p.2 <;> rfl
  change (ω.1 p.1 p.2, boolToSign (ω.2 p.1 p.2)) =
    (ω.1 p.1 p.2, HeidBridge.boolToSign (ω.2 p.1 p.2))
  rw [h]

/-- The uniform law on sketch samples is Heidary's raw selector law. -/
theorem expect_sketchLaw_toRaw {s b n : ℕ} (hb : 0 < b) (G : RawSample s b n → ℝ) :
    (sketchLaw s b n hb).expect (fun ω => G (toRaw ω)) = (rawSampleLaw s b n hb).expect G := by
  simp only [toRaw_eq_sketchRawEquiv]
  exact HeidBridge.expect_sketchLaw_eq_rawSampleLaw hb G

end Cross
end SparseStack
