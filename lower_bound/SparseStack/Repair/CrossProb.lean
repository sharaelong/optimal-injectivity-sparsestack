import SparseStack.CrossGram
import SparseStack.Repair.Defs
import SparseStack.Prob.Toolkit

/-!
# Head repair: the cross-Gram failure probability (HR2) (paper, eq. (cross-probability), lines
1010–1026)

For a fixed head set `I` and a fixed background isometry `V` supported off `I`, if the right-hand
side of eq. (refined-cross) is at most `δ_cross t₀`, then `P{‖H̃ᵀỸ‖ > t₀} ≤ δ_cross`:
`cross_gram_refined` bounds the conditional expectation for every head configuration,
`expect_mergeHead` averages over the head, and Markov's inequality concludes. If `I = ∅` or
`d = 0` the cross-Gram matrix is zero.
-/

namespace SparseStack

open SparseFock
open scoped Matrix.Norms.L2Operator

/-- The cross-Gram matrix vanishes for an empty head. -/
theorem crossGram_empty_head {s b n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ)
    (ω : SketchSample s b n) : crossGram ∅ V ω = 0 := by
  have h0 : coordProj (∅ : Finset (Fin n)) = 0 := by
    simp [coordProj]
  simp [crossGram, h0]

/-- The unconditional expectation bound `E‖H̃ᵀỸ‖ ≤ crossBound` (via `expect_mergeHead`). -/
theorem expect_crossGram_le {n s b d p : ℕ} (hb : 0 < b) (hs : 1 ≤ s) (hbs : 2 * s ≤ b)
    (I : Finset (Fin n)) (hI : 1 ≤ I.card) (V : Matrix (Fin n) (Fin d) ℝ)
    (hV : V.transpose * V = 1) (hVsupp : ∀ i ∈ I, ∀ k, V i k = 0) (hd : 1 ≤ d)
    (hp : 64 ≤ p) (hplog : Real.log (2 * d) ≤ p) :
    (sketchLaw s b n hb).expect (fun ω => ‖crossGram I V ω‖) ≤ crossBound I.card d p b s := by
  rw [expect_mergeHead hb I]
  calc (sketchLaw s b n hb).expect (fun ω₀ =>
          (sketchLaw s b n hb).expect (fun ω => ‖crossGram I V (mergeHead I ω₀ ω)‖))
      ≤ (sketchLaw s b n hb).expect (fun _ => crossBound I.card d p b s) := by
        apply FiniteLaw.expect_mono
        intro ω₀
        exact cross_gram_refined hs hbs I hI V hV hVsupp hd p hp hplog ω₀
    _ = crossBound I.card d p b s := FiniteLaw.expect_const _ _

/-- eq. (cross-probability): `P{‖H̃ᵀỸ‖ > t₀} ≤ δ_cross` whenever the refined bound is at most
`δ_cross t₀`. -/
theorem cross_prob {n s b d p : ℕ} (hb : 0 < b) (hs : 1 ≤ s) (hbs : 2 * s ≤ b) (hp : 64 ≤ p)
    (I : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ) (hV : V.transpose * V = 1)
    (hVsupp : ∀ i ∈ I, ∀ k, V i k = 0) (hplog : 1 ≤ d → Real.log (2 * d) ≤ p)
    (hbound : crossBound I.card d p b s ≤ 249 / 10000 * t0) :
    (sketchLaw s b n hb).prob {ω | t0 < ‖crossGram I V ω‖} ≤ 249 / 10000 := by
  have ht0 : (0 : ℝ) < t0 := by norm_num [t0]
  by_cases hdeg : I.card = 0 ∨ d = 0
  · -- degenerate cases: the cross-Gram matrix vanishes
    have hzero : ∀ ω : SketchSample s b n, crossGram I V ω = 0 := by
      intro ω
      rcases hdeg with hI | hd
      · rw [Finset.card_eq_zero.1 hI]
        exact crossGram_empty_head V ω
      · subst hd
        ext i k
        exact k.elim0
    have hempty : {ω : SketchSample s b n | t0 < ‖crossGram I V ω‖} = ∅ := by
      ext ω
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hω
      have hω' : t0 < ‖crossGram I V ω‖ := hω
      rw [hzero ω, norm_zero] at hω'
      linarith
    rw [hempty, FiniteLaw.prob_empty]
    norm_num
  · push Not at hdeg
    have hI : 1 ≤ I.card := Nat.one_le_iff_ne_zero.2 hdeg.1
    have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 hdeg.2
    have hE := expect_crossGram_le hb hs hbs I hI V hV hVsupp hd hp (hplog hd)
    have hmarkov := FiniteLaw.markov (sketchLaw s b n hb)
      (f := fun ω => ‖crossGram I V ω‖) (fun ω => norm_nonneg _) ht0
    have hsub : {ω : SketchSample s b n | t0 < ‖crossGram I V ω‖} ⊆
        {ω | t0 ≤ ‖crossGram I V ω‖} := by
      intro ω hω
      exact show t0 ≤ ‖crossGram I V ω‖ from le_of_lt hω
    calc (sketchLaw s b n hb).prob {ω | t0 < ‖crossGram I V ω‖}
        ≤ (sketchLaw s b n hb).prob {ω | t0 ≤ ‖crossGram I V ω‖} :=
          FiniteLaw.prob_mono _ hsub
      _ ≤ (sketchLaw s b n hb).expect (fun ω => ‖crossGram I V ω‖) / t0 := hmarkov
      _ ≤ crossBound I.card d p b s / t0 := by gcongr
      _ ≤ 249 / 10000 := by
          rw [div_le_iff₀ ht0]
          exact hbound

end SparseStack
