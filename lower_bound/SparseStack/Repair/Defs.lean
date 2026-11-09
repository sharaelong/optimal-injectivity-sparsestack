import SparseStack.Basic.Defs
import SparseStack.Prob.Sketch

/-!
# Head repair: shared definitions (W-REP)

Definitions used by the proof of `head_repair` (paper, lines 977–1111):

* `retCount I ω i` — the retained-incidence count `a_i`: the number of blocks in which `i` lies in
  a bucket containing exactly one coordinate of `I`;
* `badSet I ω = {i ∈ I : a_i < a₀ s}` and `goodSet I ω = I \ badSet I ω`;
* `coordCols G = E_G`, `wPlus G V = [E_G | V]` (the second-group background `W₊`) and the matching
  coefficient vector `wPlusCoeff G h f = (h|_G, f)`;
* `crossBound N d p b s` — the right-hand side of eq. (refined-cross) (`cross_gram_refined`);
* the block decomposition of the sample space: `BlockSample b n`, `ofBlocks`, `blockLaw`, and the
  per-block event `aloneIn I i y` (`i` is alone among `I` in its bucket).
-/

namespace SparseStack

open SparseFock

/-! ## Retention counts and the good/bad split -/

/-- The retained-incidence count `a_i`: the number of blocks `t` in which coordinate `i` lies in a
bucket containing exactly one coordinate of `I`. -/
noncomputable def retCount {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n)
    (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun t : Fin s => bucketLoad I ω t (ω.1 t i) = 1)).card

/-- The bad set `B = {i ∈ I : a_i < a₀ s}`. -/
noncomputable def badSet {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n) :
    Finset (Fin n) :=
  I.filter (fun i => (retCount I ω i : ℝ) < a0 * s)

/-- The good set `G = {i ∈ I : a_i ≥ a₀ s} = I \ B`. -/
noncomputable def goodSet {s b n : ℕ} (I : Finset (Fin n)) (ω : SketchSample s b n) :
    Finset (Fin n) :=
  I.filter (fun i => ¬ (retCount I ω i : ℝ) < a0 * s)

/-! ## The augmented background `W₊ = [E_G | V]` -/

/-- The coordinate columns `E_G ∈ ℝ^{n × |G|}` (column `j` is `e_{g_j}`). -/
noncomputable def coordCols {n : ℕ} (G : Finset (Fin n)) : Matrix (Fin n) (Fin G.card) ℝ :=
  fun i j => if i = (G.equivFin.symm j : Fin n) then 1 else 0

/-- The augmented background `W₊ = [E_G | V] ∈ ℝ^{n × (|G| + d)}`. -/
noncomputable def wPlus {n d : ℕ} (G : Finset (Fin n)) (V : Matrix (Fin n) (Fin d) ℝ) :
    Matrix (Fin n) (Fin (G.card + d)) ℝ :=
  (Matrix.fromCols (coordCols G) V).submatrix id finSumFinEquiv.symm

/-- The coefficient vector `(h|_G, f)` with `W₊ (h|_G, f) = E_G h + V f`. -/
noncomputable def wPlusCoeff {n d : ℕ} (G : Finset (Fin n)) (h : Fin n → ℝ) (f : Fin d → ℝ) :
    Fin (G.card + d) → ℝ :=
  fun k => Sum.elim (fun j : Fin G.card => h (G.equivFin.symm j : Fin n)) f (finSumFinEquiv.symm k)

/-! ## The refined cross-Gram bound -/

/-- The right-hand side of eq. (refined-cross), exactly as in `cross_gram_refined` with `N = |I|`. -/
noncomputable def crossBound (N d p b s : ℕ) : ℝ :=
  22 * Real.sqrt (2 * ((N : ℝ) + ((d : ℝ) + 2 * p + 1)) / (3 * b * s) +
      ((p : ℝ) + 1) / (s : ℝ) ^ 2) +
    2 * Real.sqrt (3 * (N : ℝ) * d / ((s : ℝ) ^ 2 * (b : ℝ) ^ 3) * (Nat.choose s 3 : ℝ))

/-! ## Block decomposition of the sample space -/

/-- One block of a sample: the hashes and the sign bits of all coordinates. -/
abbrev BlockSample (b n : ℕ) : Type := (Fin n → Fin b) × (Fin n → Bool)

/-- Reassemble a sample from its blocks. -/
def ofBlocks {s b n : ℕ} (x : Fin s → BlockSample b n) : SketchSample s b n :=
  (fun t => (x t).1, fun t => (x t).2)

/-- The uniform law on one block (requires `b ≥ 1`). -/
noncomputable def blockLaw (b n : ℕ) (hb : 0 < b) : FiniteLaw (BlockSample b n) where
  weight _ := 1 / (Fintype.card (BlockSample b n) : ℝ)
  weight_nonneg _ := by positivity
  sum_weight := by
    have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
    have hc : (Fintype.card (BlockSample b n) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

/-- `i` is alone among the coordinates of `I` in its bucket of the block `y`. -/
def aloneIn {b n : ℕ} (I : Finset (Fin n)) (i : Fin n) (y : BlockSample b n) : Prop :=
  ∀ j ∈ I, y.1 j = y.1 i → j = i

end SparseStack
