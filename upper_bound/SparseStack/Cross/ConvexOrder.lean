import SparseStack.Cross.Multiplicity

/-!
# Cross-Gram bound, step (5): entrywise convex order `U^lo ≤_cx 2 ζ_B` (W-CROSS)

* Scalar principle (paper, eq. (convex-low)): if `L` is symmetric, `|L| ≤ 2` and `E|L| ≤ 2q`, then
  for every convex `φ`, `E φ(L) ≤ (1-q) φ(0) + (q/2)(φ(2) + φ(-2))` (even part + convex
  interpolation on `[0,2]`, using `φ(2) + φ(-2) ≥ 2 φ(0)`).
* With `B = ⌊2b/s⌋` (`B s ≤ 2b`): `E|U^lo| ≤ E c = s/b ≤ 2/B`, and the right side is
  `E φ(2 ζ_B)`.
* Tensorization (`expect_le_of_convex_order`): entrywise convex order of independent entries
  transfers to every separately convex function (hybrid argument, one entry at a time,
  conditioning on the other entries).
* Application to `x ↦ ‖U^lo V‖`: `E ‖U^lo V‖ ≤ 2 E ‖X_N V‖`.
-/

namespace SparseStack
namespace Cross

open SparseFock SparseFock.SparseIIDCoupling
open scoped Matrix.Norms.L2Operator

/-- Even part and convex interpolation on `[-2, 2]`: for `|y| ≤ 2`,
`(φ(y) + φ(-y))/2 ≤ (1 - |y|/2) φ(0) + (|y|/2) (φ(2) + φ(-2))/2`. -/
theorem even_part_le_interp (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) {y : ℝ} (hy : |y| ≤ 2) :
    (φ y + φ (-y)) / 2 ≤ (1 - |y| / 2) * φ 0 + |y| / 2 * ((φ 2 + φ (-2)) / 2) := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, |y| / 2 = t := ⟨_, rfl⟩
  rw [ht]
  have ht0 : 0 ≤ t := by rw [← ht]; positivity
  have ht1 : t ≤ 1 := by rw [← ht]; linarith
  -- `φ (t z) ≤ (1 - t) φ 0 + t φ z`
  have key : ∀ z : ℝ, φ (t * z) ≤ (1 - t) * φ 0 + t * φ z := by
    intro z
    have h := hφ.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ z) (by linarith : 0 ≤ 1 - t) ht0
      (by ring)
    simpa [smul_eq_mul] using h
  have h2 := key 2
  have hm2 := key (-2)
  rcases le_total 0 y with hy0 | hy0
  · have hyt : y = t * 2 := by rw [← ht, abs_of_nonneg hy0]; ring
    have hyt' : -y = t * (-2) := by rw [hyt]; ring
    rw [hyt', hyt]
    linarith
  · have hyt : y = t * (-2) := by rw [← ht, abs_of_nonpos hy0]; ring
    have hyt' : -y = t * 2 := by rw [hyt]; ring
    rw [hyt', hyt]
    linarith

/-- Scalar convex-order principle for a symmetric variable with `|L| ≤ 2` and `E|L| ≤ 2q`. -/
theorem convex_order_symm {α : Type*} [Fintype α] (μ : FiniteLaw α) (L : α → ℝ)
    (hsymm : ∀ ψ : ℝ → ℝ, μ.expect (fun a => ψ (L a)) = μ.expect (fun a => ψ (-L a)))
    (hbd : ∀ a, |L a| ≤ 2) {q : ℝ} (hq : μ.expect (fun a => |L a|) ≤ 2 * q)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) :
    μ.expect (fun a => φ (L a)) ≤ (1 - q) * φ 0 + q / 2 * (φ 2 + φ (-2)) := by
  -- `φ(0) ≤ (φ(2) + φ(-2))/2`
  have hK : φ 0 ≤ (φ 2 + φ (-2)) / 2 := by
    have h := hφ.2 (Set.mem_univ (2 : ℝ)) (Set.mem_univ (-2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    norm_num at h
    linarith
  -- replace `φ` by its even part
  have heven : μ.expect (fun a => φ (L a)) = μ.expect (fun a => (φ (L a) + φ (-L a)) / 2) := by
    have h2 : ∀ a, (φ (L a) + φ (-L a)) / 2 = 1 / 2 * (φ (L a) + φ (-L a)) := fun a => by ring
    rw [FiniteLaw.expect_congr _ h2, FiniteLaw.expect_smul, FiniteLaw.expect_add, ← hsymm φ]
    ring
  -- convex interpolation on `[0, 2]`, in expectation
  have hE := μ.expect_mono (fun a => even_part_le_interp φ hφ (hbd a))
  have hR : μ.expect (fun a => (1 - |L a| / 2) * φ 0 + |L a| / 2 * ((φ 2 + φ (-2)) / 2)) =
      φ 0 + μ.expect (fun a => |L a|) / 2 * ((φ 2 + φ (-2)) / 2 - φ 0) := by
    have h3 : ∀ a, (1 - |L a| / 2) * φ 0 + |L a| / 2 * ((φ 2 + φ (-2)) / 2) =
        φ 0 + ((φ 2 + φ (-2)) / 2 - φ 0) / 2 * |L a| := fun a => by ring
    rw [FiniteLaw.expect_congr _ h3, FiniteLaw.expect_add, FiniteLaw.expect_const,
      FiniteLaw.expect_smul]
    ring
  rw [heven]
  have hmono := mul_le_mul_of_nonneg_right
    (show μ.expect (fun a => |L a|) / 2 ≤ q by linarith)
    (show 0 ≤ (φ 2 + φ (-2)) / 2 - φ 0 by linarith)
  calc μ.expect (fun a => (φ (L a) + φ (-L a)) / 2)
      ≤ φ 0 + μ.expect (fun a => |L a|) / 2 * ((φ 2 + φ (-2)) / 2 - φ 0) := hE.trans_eq hR
    _ ≤ φ 0 + q * ((φ 2 + φ (-2)) / 2 - φ 0) := by linarith
    _ = (1 - q) * φ 0 + q / 2 * (φ 2 + φ (-2)) := by ring

/-- `E φ(2 ζ_B) = (1 - 1/B) φ(0) + (1/(2B)) (φ(2) + φ(-2))`. -/
theorem expect_ternary_two {B : ℕ} (hB : 0 < B) (φ : ℝ → ℝ) :
    (TernaryJacobi.law B hB).expect (fun z => φ (2 * (TernaryJacobi.eta B z / Real.sqrt B))) =
      (1 - 1 / (B : ℝ)) * φ 0 + 1 / (B : ℝ) / 2 * (φ 2 + φ (-2)) := by
  have hs : Real.sqrt (B : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hB)).ne'
  simp only [FiniteLaw.expect, TernaryJacobi.law, univ_etaOutcome]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [TernaryJacobi.mass, TernaryJacobi.eta, neg_div, div_self hs, zero_div, mul_neg,
    mul_one, mul_zero]
  ring

/-- **Entrywise convex order** (paper, eq. (convex-low), refined `B = ⌊2b/s⌋`):
`E φ(U^lo_{ij}) ≤ E φ(2 ζ_B)` for every convex `φ`. -/
theorem loPart_convex_order {s b B : ℕ} (hb : 0 < b) (hB : 0 < B) (hBs : B * s ≤ 2 * b)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) :
    (rowLaw s b hb).expect (fun w => φ (loPart w)) ≤
      (TernaryJacobi.law B hB).expect (fun z => φ (2 * (TernaryJacobi.eta B z / Real.sqrt B))) := by
  rw [expect_ternary_two hB φ]
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hbpos : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  refine convex_order_symm (rowLaw s b hb) loPart ?_ abs_loPart_le_two ?_ φ hφ
  · intro ψ
    rw [← expect_rowLaw_neg hb (fun w => ψ (loPart w))]
    simp only [loPart_neg]
  · have hsb : (s : ℝ) / b ≤ 2 * (1 / B) := by
      have hBs' : (B : ℝ) * s ≤ 2 * b := by exact_mod_cast hBs
      rw [div_le_iff₀ hbpos]
      have : 2 * (1 / (B : ℝ)) * b = 2 * b / B := by ring
      rw [this, le_div_iff₀ hBpos]
      linarith
    calc (rowLaw s b hb).expect (fun w => |loPart w|)
        ≤ (rowLaw s b hb).expect (fun w => (nzCount w : ℝ)) :=
          FiniteLaw.expect_mono _ (fun w => abs_loPart_le_nzCount w)
      _ = s / b := expect_nzCount hb
      _ ≤ 2 * (1 / B) := hsb

/-- Hybrid point: entries in `S` from `h ∘ y`, the others from `g ∘ x`. -/
def hybridPoint {E α β : Type*} [DecidableEq E] (g : E → α → ℝ) (h : E → β → ℝ)
    (S : Finset E) (x : E → α) (y : E → β) : E → ℝ :=
  fun e => if e ∈ S then h e (y e) else g e (x e)

/-- **Tensorization of the convex order.** If every entry of an independent family is dominated
in convex order, then so is every separately convex function of the family. -/
theorem expect_le_of_convex_order {E α β : Type*} [Fintype E] [DecidableEq E] [Fintype α]
    [Fintype β] (μ : E → FiniteLaw α) (ν : E → FiniteLaw β) (g : E → α → ℝ) (h : E → β → ℝ)
    (hcx : ∀ e (φ : ℝ → ℝ), ConvexOn ℝ Set.univ φ →
      (μ e).expect (fun a => φ (g e a)) ≤ (ν e).expect (fun c => φ (h e c)))
    (F : (E → ℝ) → ℝ) (hF : ∀ v e, ConvexOn ℝ Set.univ (fun r => F (Function.update v e r))) :
    (FiniteLaw.independentProduct μ).expect (fun x => F (fun e => g e (x e))) ≤
      (FiniteLaw.independentProduct ν).expect (fun y => F (fun e => h e (y e))) := by
  -- `H S`: expectation of `F` at the hybrid point with the entries in `S` already replaced
  have hmix0 : ∀ x y, hybridPoint g h ∅ x y = fun e => g e (x e) := by
    intro x y
    funext e
    simp [hybridPoint]
  have hmixU : ∀ x y, hybridPoint g h Finset.univ x y = fun e => h e (y e) := by
    intro x y
    funext e
    simp [hybridPoint]
  have hH0 : (FiniteLaw.independentProduct μ).expect (fun x =>
      (FiniteLaw.independentProduct ν).expect (fun y => F (hybridPoint g h ∅ x y))) =
      (FiniteLaw.independentProduct μ).expect (fun x => F (fun e => g e (x e))) := by
    simp only [hmix0, FiniteLaw.expect_const]
  have hHuniv : (FiniteLaw.independentProduct μ).expect (fun x =>
      (FiniteLaw.independentProduct ν).expect (fun y => F (hybridPoint g h Finset.univ x y))) =
      (FiniteLaw.independentProduct ν).expect (fun y => F (fun e => h e (y e))) := by
    simp only [hmixU, FiniteLaw.expect_const]
  have hstep : ∀ (S : Finset E) (e : E), e ∉ S →
      (FiniteLaw.independentProduct μ).expect (fun x =>
        (FiniteLaw.independentProduct ν).expect (fun y => F (hybridPoint g h S x y))) ≤
      (FiniteLaw.independentProduct μ).expect (fun x =>
        (FiniteLaw.independentProduct ν).expect
          (fun y => F (hybridPoint g h (insert e S) x y))) := by
    intro S e he
    have h1 : (FiniteLaw.independentProduct μ).expect (fun x =>
        (FiniteLaw.independentProduct ν).expect (fun y => F (hybridPoint g h S x y))) =
        (FiniteLaw.independentProduct μ).expect (fun x =>
          (FiniteLaw.independentProduct ν).expect (fun y => (μ e).expect (fun a =>
            F (Function.update (hybridPoint g h S x y) e (g e a))))) := by
      rw [expect_resample_one μ e]
      apply FiniteLaw.expect_congr
      intro x
      rw [expect_comm (μ e) (FiniteLaw.independentProduct ν)]
      apply FiniteLaw.expect_congr
      intro y
      apply FiniteLaw.expect_congr
      intro a
      congr 1
      funext e'
      by_cases he' : e' = e
      · subst he'
        simp [hybridPoint, he]
      · simp [hybridPoint, Function.update_of_ne he']
    have h2 : (FiniteLaw.independentProduct μ).expect (fun x =>
        (FiniteLaw.independentProduct ν).expect
          (fun y => F (hybridPoint g h (insert e S) x y))) =
        (FiniteLaw.independentProduct μ).expect (fun x =>
          (FiniteLaw.independentProduct ν).expect (fun y => (ν e).expect (fun c =>
            F (Function.update (hybridPoint g h S x y) e (h e c))))) := by
      apply FiniteLaw.expect_congr
      intro x
      rw [expect_resample_one ν e]
      apply FiniteLaw.expect_congr
      intro y
      apply FiniteLaw.expect_congr
      intro c
      congr 1
      funext e'
      by_cases he' : e' = e
      · subst he'
        simp [hybridPoint]
      · simp [hybridPoint, he']
    rw [h1, h2]
    apply FiniteLaw.expect_mono
    intro x
    apply FiniteLaw.expect_mono
    intro y
    exact hcx e (fun r => F (Function.update (hybridPoint g h S x y) e r))
      (hF (hybridPoint g h S x y) e)
  have hall : ∀ S : Finset E,
      (FiniteLaw.independentProduct μ).expect (fun x =>
        (FiniteLaw.independentProduct ν).expect (fun y => F (hybridPoint g h ∅ x y))) ≤
      (FiniteLaw.independentProduct μ).expect (fun x =>
        (FiniteLaw.independentProduct ν).expect (fun y => F (hybridPoint g h S x y))) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact le_rfl
    | insert e S he ih => exact ih.trans (hstep S e he)
  rw [← hH0, ← hHuniv]
  exact hall Finset.univ

/-- The matrix with entries `v (i, j)` in the rows of `I` (zero elsewhere). -/
def rowsOf {n : ℕ} (I : Finset (Fin n)) (v : Fin n × Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i ∈ I then v (i, j) else 0

/-- `rowsOf` is affine in each entry. -/
theorem rowsOf_update {n : ℕ} (I : Finset (Fin n)) (v : Fin n × Fin n → ℝ)
    (e : Fin n × Fin n) (r : ℝ) :
    rowsOf I (Function.update v e r) =
      rowsOf I (Function.update v e 0) + r • rowsOf I (Pi.single e 1) := by
  ext i j
  simp only [rowsOf, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hi : i ∈ I
  · by_cases hij : (i, j) = e
    · subst hij
      simp [hi]
    · simp [hi, hij]
  · simp [hi]

/-- **Step (5)**: `E ‖U^lo V‖ ≤ 2 E ‖X_N V‖`. -/
theorem lo_comparison {s b n d B : ℕ} (hb : 0 < b) (hB : 0 < B) (hBs : B * s ≤ 2 * b)
    (I : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ) :
    (aggLaw s n b hb).expect (fun x => ‖loMat I x * V‖) ≤
      2 * (ternLaw n B hB).expect (fun z => ‖ternMat B I z * V‖) := by
  -- `r ↦ ‖rowsOf I (update v e r) * V‖` is convex
  have hF : ∀ (v : Fin n × Fin n → ℝ) (e : Fin n × Fin n),
      ConvexOn ℝ Set.univ (fun r => ‖rowsOf I (Function.update v e r) * V‖) := by
    intro v e
    have hfun : (fun r => ‖rowsOf I (Function.update v e r) * V‖) =
        (fun r => ‖rowsOf I (Function.update v e 0) * V + r • (rowsOf I (Pi.single e 1) * V)‖) := by
      funext r
      rw [rowsOf_update, Matrix.add_mul, Matrix.smul_mul]
    rw [hfun]
    exact convexOn_norm_add_smul _ _
  have key := expect_le_of_convex_order (fun _ : Fin n × Fin n => rowLaw s b hb)
    (fun _ : Fin n × Fin n => TernaryJacobi.law B hB)
    (fun _ w => loPart w) (fun _ z => 2 * (TernaryJacobi.eta B z / Real.sqrt B))
    (fun _ φ hφ => loPart_convex_order hb hB hBs φ hφ)
    (fun v => ‖rowsOf I v * V‖) hF
  have hR : ∀ z : Fin n × Fin n → EtaOutcome,
      rowsOf I (fun e => 2 * (TernaryJacobi.eta B (z e) / Real.sqrt B)) =
        (2 : ℝ) • ternMat B I z := by
    intro z
    ext i j
    simp only [rowsOf, ternMat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  calc (aggLaw s n b hb).expect (fun x => ‖loMat I x * V‖)
      = (FiniteLaw.independentProduct (fun _ : Fin n × Fin n => rowLaw s b hb)).expect
          (fun x => ‖rowsOf I (fun e => loPart (x e)) * V‖) := rfl
    _ ≤ (FiniteLaw.independentProduct (fun _ : Fin n × Fin n => TernaryJacobi.law B hB)).expect
          (fun z => ‖rowsOf I (fun e => 2 * (TernaryJacobi.eta B (z e) / Real.sqrt B)) * V‖) :=
        key
    _ = (ternLaw n B hB).expect (fun z => 2 * ‖ternMat B I z * V‖) := by
        apply FiniteLaw.expect_congr
        intro z
        rw [hR, Matrix.smul_mul, norm_smul, Real.norm_eq_abs, abs_two]
    _ = 2 * (ternLaw n B hB).expect (fun z => ‖ternMat B I z * V‖) :=
        FiniteLaw.expect_smul _ 2 _

end Cross
end SparseStack
