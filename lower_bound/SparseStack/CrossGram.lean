import SparseStack.IidNorm
import SparseStack.Prob.Sketch
import SparseStack.Cross.Structure
import SparseStack.Cross.Coupling
import SparseStack.Cross.Restore
import SparseStack.Cross.ConvexOrder
import SparseStack.Cross.Padding
import SparseStack.Cross.Numerics

/-!
# Selector coupling and the refined unique-head cross-Gram bound
(paper, lines 631–775 and 800–869)

Setting (support form): an `s`-block stack with `b ≥ 2s`; head coordinates `I` (`|I| = N ≥ 1`);
the background is a fixed isometry `V ∈ ℝ^{n×d}` supported off `I` (rows in `I` are zero),
`d ≥ 1`. `T` retains exactly the output rows containing one coordinate of `I`; the cross-Gram is
`crossGram I V ω = (T Π E_I)ᵀ (T Π V)` (`Basic/Defs.lean`). Conditioning on the head (all hashes
and signs of coordinates in `I`) is averaging over `ω` in `mergeHead I ω₀ ω`.

Refined bound (eq. (refined-cross)), for every head configuration `ω₀` and integer
`p ≥ max{64, log(2d)}`:
`E[‖H̃ᵀỸ‖ | head] ≤ 22 √(2(N + D_p)/(3bs) + (p+1)/s²) + 2 √(3Nd/(s²b³) · C(s,3))`.

Proof outline: structure `H̃ᵀỸ = s⁻¹ ∑_{t,j} A_t ξ_{tj} w_jᵀ`; selector coupling
(`E[ζ|ξ] = c_b⁻¹ ξ`, Heidary's `SparseIIDCoupling`, `c_b < 19/12`) and conditional Jensen
(triangle inequality for finite averages); restore entries with `α_{ti} = 0` (Jensen); split
`U = U^lo + U^hi` by multiplicity; Frobenius bound for `U^hi`; entrywise convex order
`V ≤_cx 2ζ_B` with `B = ⌊2b/s⌋ ≥ 3b/(2s)`; pad rows to `m = aB`, `a = ⌈N/B⌉`; apply
`iid_norm_refined`; `2 c_b √46 < 22`.
-/

namespace SparseStack

open SparseFock
open scoped Matrix.Norms.L2Operator

namespace Cross

open SparseFock.SparseIIDCoupling

/-- Steps (6)–(7): padding to `m = aB` rows, `iid_norm_refined` and Cauchy–Schwarz:
`E ‖X_N V‖ ≤ √(46 (a + D_p/B + p))`. -/
theorem tern_norm_le {n d a B : ℕ} (hB : 1 < B) (ha : 1 ≤ a) (I : Finset (Fin n))
    (hIa : I.card ≤ a * B) (V : Matrix (Fin n) (Fin d) ℝ) (hV : V.transpose * V = 1)
    (hd : 1 ≤ d) (p : ℕ) (hp : 64 ≤ p) (hplog : Real.log (2 * d) ≤ p) :
    (ternLaw n B (Nat.zero_lt_of_lt hB)).expect (fun z => ‖ternMat B I z * V‖) ≤
      Real.sqrt (46 * ((a : ℝ) + ((d : ℝ) + 2 * p + 1) / B + p)) := by
  have hm : 0 < a * B := Nat.mul_pos (by omega) (by omega)
  calc (ternLaw n B (Nat.zero_lt_of_lt hB)).expect (fun z => ‖ternMat B I z * V‖)
      ≤ (ProductFock.iidLaw B hB (a * B) n).expect (fun x => ‖iidMat B x * V‖) :=
        pad_comparison hB I hIa hm V
    _ ≤ Real.sqrt ((ProductFock.iidLaw B hB (a * B) n).expect
          (fun x => ‖iidMat B x * V‖ ^ 2)) := expect_le_sqrt_expect_sq _ _
    _ ≤ Real.sqrt (46 * ((a : ℝ) + ((d : ℝ) + 2 * p + 1) / B + p)) :=
        Real.sqrt_le_sqrt (iid_norm_refined hB ha V hV hd p hp hplog)

end Cross

open _root_.SparseStack.Cross SparseFock.SparseIIDCoupling SparseFock.SparseStackDistribution in
/-- The refined unique-head cross-Gram bound (eq. (refined-cross)), conditionally on the head. -/
theorem cross_gram_refined {n s b d : ℕ} (hs : 1 ≤ s) (hbs : 2 * s ≤ b)
    (I : Finset (Fin n)) (hI : 1 ≤ I.card) (V : Matrix (Fin n) (Fin d) ℝ)
    (hV : V.transpose * V = 1) (hVsupp : ∀ i ∈ I, ∀ k, V i k = 0) (hd : 1 ≤ d) (p : ℕ)
    (hp : 64 ≤ p) (hplog : Real.log (2 * d) ≤ p) (ω₀ : SketchSample s b n) :
    (sketchLaw s b n (by omega)).expect (fun ω => ‖crossGram I V (mergeHead I ω₀ ω)‖) ≤
      22 * Real.sqrt (2 * ((I.card : ℝ) + ((d : ℝ) + 2 * p + 1)) / (3 * b * s) +
          ((p : ℝ) + 1) / (s : ℝ) ^ 2) +
        2 * Real.sqrt (3 * (I.card : ℝ) * d / ((s : ℝ) ^ 2 * (b : ℝ) ^ 3) * (Nat.choose s 3 : ℝ)) := by
  have hb : 0 < b := by omega
  -- `B = ⌊2b/s⌋ ≥ 3b/(2s) ≥ 3`
  have hB3 : (3 * b : ℝ) / (2 * s) ≤ ((2 * b / s : ℕ) : ℝ) := div_floor_ge hs hbs
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hbsR : (2 * s : ℝ) ≤ b := by exact_mod_cast hbs
  have hB1 : 1 < 2 * b / s := by
    have h3 : (3 : ℝ) ≤ (3 * b : ℝ) / (2 * s) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have : (1 : ℝ) < ((2 * b / s : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have hB0 : 0 < 2 * b / s := Nat.zero_lt_of_lt hB1
  have hBs : 2 * b / s * s ≤ 2 * b := Nat.div_mul_le_self (2 * b) s
  -- `a = ⌊N/B⌋ + 1`: `N ≤ aB`, `a ≤ N/B + 1`
  have hIa : I.card ≤ (I.card / (2 * b / s) + 1) * (2 * b / s) := by
    have h1 := Nat.div_add_mod I.card (2 * b / s)
    have h2 := Nat.mod_lt I.card hB0
    nlinarith
  have haR : ((I.card / (2 * b / s) + 1 : ℕ) : ℝ) ≤
      (I.card : ℝ) / ((2 * b / s : ℕ) : ℝ) + 1 := by
    have : ((I.card / (2 * b / s) : ℕ) : ℝ) ≤ (I.card : ℝ) / ((2 * b / s : ℕ) : ℝ) :=
      Nat.cast_div_le
    push_cast
    linarith
  -- the chain
  have hstruct : (sketchLaw s b n (by omega)).expect
      (fun ω => ‖crossGram I V (mergeHead I ω₀ ω)‖) =
      (rawSampleLaw s b n hb).expect (fun z => ‖structMat I ω₀ V (fun p => selVec (z p))‖) := by
    rw [← expect_sketchLaw_toRaw hb]
    apply FiniteLaw.expect_congr
    intro ω
    rw [crossGram_mergeHead_eq I V hVsupp ω₀ ω]
  have hagg : (aggLaw s n b hb).expect (fun x => ‖(s : ℝ)⁻¹ • (fullMat I x * V)‖) ≤
      (s : ℝ)⁻¹ * (2 * (ternLaw n (2 * b / s) hB0).expect (fun z => ‖ternMat (2 * b / s) I z * V‖) +
        (aggLaw s n b hb).expect (fun x => ‖hiMat I x * V‖)) := by
    refine (expect_norm_fullMat_le hb I V).trans ?_
    gcongr
    exact lo_comparison hb hB0 hBs I V
  rw [hstruct]
  calc (rawSampleLaw s b n hb).expect (fun z => ‖structMat I ω₀ V (fun p => selVec (z p))‖)
      ≤ cB b * (coupledLaw s n b hb).expect
          (fun y => ‖structMat I ω₀ V (fun p u => yValue (y p u))‖) := coupling_bound hb I ω₀ V
    _ ≤ cB b * (aggLaw s n b hb).expect (fun x => ‖(s : ℝ)⁻¹ • (fullMat I x * V)‖) :=
        mul_le_mul_of_nonneg_left (restore_bound hb I ω₀ V) (cB_pos hb).le
    _ ≤ cB b * ((s : ℝ)⁻¹ * (2 * (ternLaw n (2 * b / s) hB0).expect
          (fun z => ‖ternMat (2 * b / s) I z * V‖) +
          (aggLaw s n b hb).expect (fun x => ‖hiMat I x * V‖))) :=
        mul_le_mul_of_nonneg_left hagg (cB_pos hb).le
    _ ≤ _ := final_combine hsR (by positivity) hB3 haR (by positivity) (by positivity)
        (by positivity) (cB_pos hb).le (cB_le_two hb) (two_mul_cB_mul_sqrt_46_le hb)
        (tern_norm_le hB1 (Nat.le_add_left 1 _) I hIa V hV hd p hp hplog)
        (expect_norm_hiMat_le hb I V hV)

end SparseStack
