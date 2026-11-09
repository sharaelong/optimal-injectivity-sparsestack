import SparseStack.Repair.Certificate
import SparseStack.Repair.Retention

/-!
# Head repair: the two certificates (eq. (first-certificate), eq. (second-certificate))
(paper, lines 1049–1093)

Both certificates follow from `cert_core` (deleting rows, completing the square, operator norm of
the cross-Gram matrix) and W-SKETCH's `retained_head_gram` (the retained head Gram is
`diag(a_i/s)`):

* `first_certificate`: head `I`, background `V`; on `‖crossGram I V ω‖ ≤ t₀`,
  `(a₀ - t₀) ‖h_G‖² - t₀ ‖h_B‖² ≤ ‖Π₁(h + V f)‖² + t₀ ‖f‖²`;
* `second_certificate`: head `B`, background `W₊ = [E_G | V]`; on `‖crossGram B W₊ ω‖ ≤ t₀` and
  full retention of `B`, `(a₀ - t₀) ‖h_B‖² ≤ ‖Π₂(h + V f)‖² + t₀ (‖h_G‖² + ‖f‖²)`.
-/

namespace SparseStack

open Matrix
open scoped Matrix.Norms.L2Operator

/-- For `h` supported on `I`: `‖h‖² = ‖h_G‖² + ‖h_B‖²`. -/
theorem sqNorm_eq_good_add_bad {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n)
    (h : Fin n → ℝ) (hh : ∀ i, i ∉ I → h i = 0) :
    sqNorm h = ∑ i ∈ goodSet I ω, h i ^ 2 + ∑ i ∈ badSet I ω, h i ^ 2 := by
  have h1 : sqNorm h = ∑ i ∈ I, h i ^ 2 := by
    unfold sqNorm dotProduct
    rw [Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [hh i hi])]
    simp only [sq]
  have h2 := Finset.sum_union (disjoint_badSet_goodSet I ω) (f := fun i => h i ^ 2)
  rw [badSet_union_goodSet] at h2
  rw [h1, h2, add_comm]

/-- eq. (first-certificate): `(a₀ - t₀) ‖h_G‖² - t₀ ‖h_B‖² ≤ ‖Π₁(h + V f)‖² + t₀ ‖f‖²`. -/
theorem first_certificate {s b n d : ℕ} (hs : 0 < s) (I : Finset (Fin n))
    (V : Matrix (Fin n) (Fin d) ℝ) (ω : SketchSample s b n) (hM : ‖crossGram I V ω‖ ≤ t0)
    (h : Fin n → ℝ) (hh : ∀ i, i ∉ I → h i = 0) (f : Fin d → ℝ) :
    (a0 - t0) * ∑ i ∈ goodSet I ω, h i ^ 2 - t0 * ∑ i ∈ badSet I ω, h i ^ 2 ≤
      sqNorm ((sketchMatrix ω).mulVec (h + V.mulVec f)) + t0 * sqNorm f := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have core := cert_core I V ω hM h hh f
  have gram := retained_head_gram I ω h hh
  rw [← Matrix.mulVec_mulVec] at gram
  rw [gram] at core
  have hsplitI := Finset.sum_union (disjoint_badSet_goodSet I ω)
    (f := fun i => (retCount I ω i : ℝ) / s * h i ^ 2)
  rw [badSet_union_goodSet] at hsplitI
  have hbad : 0 ≤ ∑ i ∈ badSet I ω, (retCount I ω i : ℝ) / s * h i ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hgood : a0 * ∑ i ∈ goodSet I ω, h i ^ 2 ≤
      ∑ i ∈ goodSet I ω, (retCount I ω i : ℝ) / s * h i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hi' : ¬ (retCount I ω i : ℝ) < a0 * s := (Finset.mem_filter.1 hi).2
    have ha : a0 ≤ (retCount I ω i : ℝ) / s := by
      rw [le_div_iff₀ hs']
      linarith [not_lt.1 hi']
    exact mul_le_mul_of_nonneg_right ha (sq_nonneg _)
  have hnorm := sqNorm_eq_good_add_bad I ω h hh
  rw [hnorm] at core
  linarith

/-- eq. (second-certificate): with head `B` and background `W₊ = [E_G | V]`, if every coordinate
of `B` has at least `a₀ s` retained incidences, then for `h` supported on `B ∪ G` and all `f`,
`(a₀ - t₀) ‖h_B‖² ≤ ‖Π₂(h + V f)‖² + t₀ (‖h_G‖² + ‖f‖²)`. -/
theorem second_certificate {s b n d : ℕ} (hs : 0 < s) (B G : Finset (Fin n))
    (hBG : Disjoint B G) (V : Matrix (Fin n) (Fin d) ℝ) (ω : SketchSample s b n)
    (hM : ‖crossGram B (wPlus G V) ω‖ ≤ t0) (hret : ∀ i ∈ B, a0 * s ≤ retCount B ω i)
    (h : Fin n → ℝ) (hh : ∀ i, i ∉ B ∪ G → h i = 0) (f : Fin d → ℝ) :
    (a0 - t0) * ∑ i ∈ B, h i ^ 2 ≤
      sqNorm ((sketchMatrix ω).mulVec (h + V.mulVec f)) + t0 * (∑ i ∈ G, h i ^ 2 + sqNorm f) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsplit := split_wPlus B G hBG V h hh f
  have hhB : ∀ i, i ∉ B → restrictVec B h i = 0 := fun i hi => by simp [restrictVec, hi]
  have core := cert_core B (wPlus G V) ω hM (restrictVec B h) hhB (wPlusCoeff G h f)
  have gram := retained_head_gram B ω (restrictVec B h) hhB
  rw [← Matrix.mulVec_mulVec] at gram
  rw [gram, ← hsplit, sqNorm_wPlusCoeff, sqNorm_restrictVec] at core
  have hge : a0 * ∑ i ∈ B, h i ^ 2 ≤
      ∑ i ∈ B, (retCount B ω i : ℝ) / s * restrictVec B h i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hri : restrictVec B h i = h i := by simp [restrictVec, hi]
    rw [hri]
    have ha : a0 ≤ (retCount B ω i : ℝ) / s := by
      rw [le_div_iff₀ hs']
      linarith [hret i hi]
    exact mul_le_mul_of_nonneg_right ha (sq_nonneg _)
  linarith

end SparseStack
