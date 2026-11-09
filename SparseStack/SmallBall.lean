import SparseStack.Prob.Sketch
import SparseStack.SmallBall.Hash
import SparseStack.SmallBall.Sign

/-!
# Physical small ball (paper, Lemma `lem:smallball`, lines 198–297)

Only the form without deletion (`T = I`, `𝓗` = everything) is used (Theorem `thm:localization`,
line 421), so that is the contract. `c_ph² = 2/81`, `c_sb = 1/3200`.

Proof outline (paper): `p_i = z_i²`, bucket masses `W_{tu}`, `𝓛 = ∑_{t,u} (W_{tu} - 10/D)_+`;
`E 𝓛 ≤ s/20`; bounded differences (McDiarmid) gives `P{𝓛 > s/16} ≤ e^{-sD/3200}`; on the
complement the retained buckets (`W_{tu} ≤ 20/D`) have `z`-variance `V ≥ 3s/4`, `v_max ≤ 20/D`;
conditionally on hashes and on the signs of `supp h`, Paley–Zygmund (threshold 1/3, fourth moment
`≤ 3 (second)²`) gives `P{(y+X₀)² ≥ a²v/3} ≥ 4/27` per retained bucket, independently across
buckets; the weighted Bernoulli bound gives sign failure `≤ e^{-11 sD/34560} ≤ e^{-sD/3200}`.

Lean proof (helper files under `SparseStack/SmallBall/`):
* `Defs.lean`: the uniform sketch law is hashes × signs (`sketchLaw_prob_eq`), and
  `‖Π w‖² = (1/s) ∑_{t,u} bucketOut²` (`sqNorm_sketch_eq`);
* `Hash.lean`: `hash_step`, `P{𝓛 > s/16} ≤ e^{-sD/3200}`;
* `Rademacher.lean`, `Sign.lean`: `sign_step`, for every hash outcome with `𝓛 ≤ s/16` the sign
  failure probability is `≤ e^{-sD/3200}`. Each bucket output is one Rademacher sum (no
  conditioning on the signs of `supp h` is needed; see `Rademacher.lean`), and the retained
  mass satisfies `V ≥ 7s/8`.
* Here: Fubini over hashes, then `P ≤ P{𝓛 > s/16} + sup_{𝓛 ≤ s/16} P_σ ≤ 2 e^{-sD/3200}`.
-/

namespace SparseStack

open SparseFock

/-- Lemma `lem:smallball` (no deletion): for deterministic `w = h + a z` with disjoint supports,
`a > 0`, `‖z‖ = 1`, `1 ≤ D ≤ b`, `‖z‖_∞² ≤ 1/D`:
`P{‖Π_{s,b} w‖² < (2/81) a²} ≤ 2 e^{-sD/3200}`. -/
theorem small_ball {s b n : ℕ} (hs : 0 < s) (hb : 0 < b) (h z : Fin n → ℝ) (a : ℝ) (ha : 0 < a)
    (hdisj : ∀ i, h i = 0 ∨ z i = 0) (hz : sqNorm z = 1) (D : ℝ) (hD1 : 1 ≤ D) (hDb : D ≤ b)
    (hzinf : ∀ i, z i ^ 2 ≤ 1 / D) :
    (sketchLaw s b n hb).prob
        {ω | sqNorm ((sketchMatrix ω).mulVec (h + a • z)) < 2 / 81 * a ^ 2} ≤
      2 * Real.exp (-((s : ℝ) * D) / 3200) := by
  have hz1 : ∑ i, z i ^ 2 = 1 := by
    rw [← hz]
    unfold sqNorm dotProduct
    exact Finset.sum_congr rfl (fun i _ => sq (z i))
  rw [SmallBallAux.sketchLaw_prob_eq hb]
  -- conditional failure probability given the hashes
  have hbound : ∀ x : Fin s × Fin n → Fin b,
      (SmallBallAux.signLaw s n).prob {y | SmallBallAux.toSample x y ∈
          {ω : SketchSample s b n | sqNorm ((sketchMatrix ω).mulVec (h + a • z)) <
            2 / 81 * a ^ 2}} ≤
        FiniteLaw.indicator {x | (s : ℝ) / 16 < SmallBallAux.excessMass z D x} x +
          Real.exp (-((s : ℝ) * D) / 3200) := by
    intro x
    by_cases hx : x ∈ {x : Fin s × Fin n → Fin b | (s : ℝ) / 16 < SmallBallAux.excessMass z D x}
    · rw [indicator_of_mem hx]
      have h1 := FiniteLaw.prob_le_one (SmallBallAux.signLaw s n) {y | SmallBallAux.toSample x y ∈
          {ω : SketchSample s b n | sqNorm ((sketchMatrix ω).mulVec (h + a • z)) <
            2 / 81 * a ^ 2}}
      have h2 := Real.exp_pos (-((s : ℝ) * D) / 3200)
      linarith
    · rw [indicator_of_notMem hx, zero_add]
      have hx' : SmallBallAux.excessMass z D x ≤ (s : ℝ) / 16 := by
        simp only [Set.mem_ofPred_eq, not_lt] at hx
        exact hx
      have hset : {y | SmallBallAux.toSample x y ∈
          {ω : SketchSample s b n | sqNorm ((sketchMatrix ω).mulVec (h + a • z)) <
            2 / 81 * a ^ 2}} =
          {y | 1 / (s : ℝ) * ∑ t, ∑ u, SmallBallAux.bucketOut (h + a • z) x y t u ^ 2 <
            2 / 81 * a ^ 2} := by
        ext y
        simp only [Set.mem_ofPred_eq]
        rw [SmallBallAux.sqNorm_sketch_eq]
      rw [hset]
      exact SmallBallAux.sign_step hs h z a ha hdisj hz1 D hD1 x hx'
  calc (SmallBallAux.hashLaw s b n hb).expect (fun x => (SmallBallAux.signLaw s n).prob
          {y | SmallBallAux.toSample x y ∈
            {ω : SketchSample s b n | sqNorm ((sketchMatrix ω).mulVec (h + a • z)) <
              2 / 81 * a ^ 2}})
      ≤ (SmallBallAux.hashLaw s b n hb).expect (fun x =>
          FiniteLaw.indicator {x | (s : ℝ) / 16 < SmallBallAux.excessMass z D x} x +
            Real.exp (-((s : ℝ) * D) / 3200)) := FiniteLaw.expect_mono _ hbound
    _ = (SmallBallAux.hashLaw s b n hb).expect
          (FiniteLaw.indicator {x | (s : ℝ) / 16 < SmallBallAux.excessMass z D x}) +
            Real.exp (-((s : ℝ) * D) / 3200) := by
        rw [FiniteLaw.expect_add, FiniteLaw.expect_const]
    _ ≤ Real.exp (-((s : ℝ) * D) / 3200) + Real.exp (-((s : ℝ) * D) / 3200) :=
        add_le_add (SmallBallAux.hash_step hs hb z hz1 D hD1 hDb hzinf) le_rfl
    _ = 2 * Real.exp (-((s : ℝ) * D) / 3200) := by ring

end SparseStack
