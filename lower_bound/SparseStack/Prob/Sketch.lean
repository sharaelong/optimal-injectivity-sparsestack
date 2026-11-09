import SparseStack.Basic.Defs
import SparseFockFormal.FiniteProbability

/-!
# The SparseStack sample space as a finite law (lead-owned interface)

* `sketchLaw s b n hb`: the uniform law on `SketchSample s b n`; `uniformProb` of the spec is its
  `prob` (`uniformProb_eq_prob`).
* Block groups: `blockRestrict f ω` keeps the blocks `f t` (t : Fin q) of `ω`. Disjoint groups are
  independent (`two_stage_independence`).
* Head/background conditioning: `mergeHead I ω₀ ω` (see `Basic/Defs.lean`); averaging over `ω` is
  the conditional expectation given the head `ω₀|_I` (`expect_mergeHead`).

## Proof notes (W-SKETCH)

* `sketchLaw_expect_eq_sum`: expectations under `sketchLaw` are normalized sums, so everything
  below is finite counting.
* Disjoint block groups: `blockGroupsEquiv` identifies the sample space with
  `(SketchSample q₁ b n × SketchSample q₂ b n) × (remaining blocks)`, with first component
  `(blockRestrict f₁ ω, blockRestrict f₂ ω)`. Hence the pair of restrictions is uniform on the
  product (`sketchLaw_expect_blockRestrict_pair`), which is Fubini for the two groups.
* Head conditioning: `(ω₀, ω) ↦ (mergeHead I ω₀ ω, mergeHead I ω ω₀)` is an involution of pairs
  of samples, hence a bijection; summing `F` of its first component gives `expect_mergeHead`.
-/

namespace SparseStack

open SparseFock

/-- The uniform law on the SparseStack sample space (requires `b ≥ 1`). -/
noncomputable def sketchLaw (s b n : ℕ) (hb : 0 < b) : FiniteLaw (SketchSample s b n) where
  weight _ := 1 / (Fintype.card (SketchSample s b n) : ℝ)
  weight_nonneg _ := by positivity
  sum_weight := by
    haveI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
    have hc : (Fintype.card (SketchSample s b n) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

/-! ### Counting helpers (W-SKETCH) -/

/-- The sample space is nonempty when `b ≥ 1`. -/
theorem sketchSample_nonempty {s b n : ℕ} (hb : 0 < b) : Nonempty (SketchSample s b n) := by
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  infer_instance

/-- The number of sample points is nonzero when `b ≥ 1`. -/
theorem card_sketchSample_ne_zero {s b n : ℕ} (hb : 0 < b) :
    (Fintype.card (SketchSample s b n) : ℝ) ≠ 0 := by
  have := sketchSample_nonempty (s := s) (n := n) hb
  exact_mod_cast Fintype.card_ne_zero

/-- Expectations under `sketchLaw` are normalized sums. -/
theorem sketchLaw_expect_eq_sum {s b n : ℕ} (hb : 0 < b) (F : SketchSample s b n → ℝ) :
    (sketchLaw s b n hb).expect F =
      (∑ ω, F ω) / (Fintype.card (SketchSample s b n) : ℝ) := by
  unfold FiniteLaw.expect
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  show 1 / (Fintype.card (SketchSample s b n) : ℝ) * F ω =
    F ω / (Fintype.card (SketchSample s b n) : ℝ)
  ring

private theorem indicator_of_mem' {α : Type*} {S : Set α} {x : α} (h : x ∈ S) :
    FiniteLaw.indicator S x = 1 := by
  simp [FiniteLaw.indicator, h]

private theorem indicator_of_not_mem' {α : Type*} {S : Set α} {x : α} (h : x ∉ S) :
    FiniteLaw.indicator S x = 0 := by
  simp [FiniteLaw.indicator, h]

/-- The spec's counting probability is the probability under `sketchLaw`. -/
theorem uniformProb_eq_prob {s b n : ℕ} (hb : 0 < b) (E : SketchSample s b n → Prop) :
    uniformProb (SketchSample s b n) E = (sketchLaw s b n hb).prob {ω | E ω} := by
  classical
  rw [FiniteLaw.prob, sketchLaw_expect_eq_sum, uniformProb]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : ∀ ω, FiniteLaw.indicator {ω | E ω} ω = if E ω then (1 : ℝ) else 0 := by
    intro ω
    by_cases hω : E ω
    · rw [if_pos hω]
      exact indicator_of_mem' hω
    · rw [if_neg hω]
      exact indicator_of_not_mem' hω
  simp only [h]
  rw [Finset.sum_boole]

/-- Keep the blocks `f t`, `t : Fin q`, of a sample. -/
def blockRestrict {s q b n : ℕ} (f : Fin q → Fin s) (ω : SketchSample s b n) :
    SketchSample q b n :=
  (fun t i => ω.1 (f t) i, fun t i => ω.2 (f t) i)

/-! ### Disjoint block groups (W-SKETCH) -/

/-- One block of a sample: its hash row and its sign row. -/
abbrev SketchBlock (b n : ℕ) : Type := (Fin n → Fin b) × (Fin n → Bool)

/-- A sample point as a function from blocks to block data. -/
def sketchSampleEquivBlocks (s b n : ℕ) : SketchSample s b n ≃ (Fin s → SketchBlock b n) where
  toFun ω t := (ω.1 t, ω.2 t)
  invFun x := (fun t => (x t).1, fun t => (x t).2)
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
/-- Split the index type `ι` into the range of an injective map `g : κ → ι` and its
complement. -/
noncomputable def rangeSumComplEquiv {κ ι : Type} (g : κ → ι) (hg : Function.Injective g) :
    κ ⊕ {i // i ∉ Set.range g} ≃ ι :=
  (Equiv.sumCongr (Equiv.ofInjective g hg) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun i => i ∈ Set.range g))

theorem rangeSumComplEquiv_inl {κ ι : Type} (g : κ → ι) (hg : Function.Injective g) (k : κ) :
    rangeSumComplEquiv g hg (Sum.inl k) = g k :=
  rfl

open Classical in
/-- Two disjoint block groups and the remaining blocks: the sample space is the product of the
two group sample spaces and the space of the remaining blocks. -/
noncomputable def blockGroupsEquiv {s q₁ q₂ : ℕ} (b n : ℕ) (f₁ : Fin q₁ → Fin s)
    (f₂ : Fin q₂ → Fin s) (hg : Function.Injective (Sum.elim f₁ f₂)) :
    SketchSample s b n ≃ (SketchSample q₁ b n × SketchSample q₂ b n) ×
      ({t // t ∉ Set.range (Sum.elim f₁ f₂)} → SketchBlock b n) :=
  (sketchSampleEquivBlocks s b n).trans <|
    ((rangeSumComplEquiv _ hg).symm.arrowCongr (Equiv.refl _)).trans <|
      (Equiv.sumArrowEquivProdArrow _ _ _).trans <|
        Equiv.prodCongr
          ((Equiv.sumArrowEquivProdArrow _ _ _).trans
            (Equiv.prodCongr (sketchSampleEquivBlocks q₁ b n).symm
              (sketchSampleEquivBlocks q₂ b n).symm))
          (Equiv.refl _)

theorem blockGroupsEquiv_fst {s q₁ q₂ : ℕ} (b n : ℕ) (f₁ : Fin q₁ → Fin s)
    (f₂ : Fin q₂ → Fin s) (hg : Function.Injective (Sum.elim f₁ f₂)) (ω : SketchSample s b n) :
    (blockGroupsEquiv b n f₁ f₂ hg ω).1 = (blockRestrict f₁ ω, blockRestrict f₂ ω) :=
  rfl

/-- Counting form of the independence of two disjoint block groups. -/
theorem sum_blockRestrict_pair {s q₁ q₂ b n : ℕ} (f₁ : Fin q₁ → Fin s)
    (f₂ : Fin q₂ → Fin s) (hg : Function.Injective (Sum.elim f₁ f₂))
    (G : SketchSample q₁ b n → SketchSample q₂ b n → ℝ) :
    (∑ ω : SketchSample s b n, G (blockRestrict f₁ ω) (blockRestrict f₂ ω)) *
        ((Fintype.card (SketchSample q₁ b n) : ℝ) * Fintype.card (SketchSample q₂ b n)) =
      (Fintype.card (SketchSample s b n) : ℝ) * ∑ ω₁, ∑ ω₂, G ω₁ ω₂ := by
  classical
  have hsum : ∑ ω : SketchSample s b n, G (blockRestrict f₁ ω) (blockRestrict f₂ ω) =
      ∑ x : (SketchSample q₁ b n × SketchSample q₂ b n) ×
        ({t // t ∉ Set.range (Sum.elim f₁ f₂)} → SketchBlock b n), G x.1.1 x.1.2 :=
    Fintype.sum_equiv (blockGroupsEquiv b n f₁ f₂ hg) _ _
      (fun ω => by rw [blockGroupsEquiv_fst])
  have hcard : Fintype.card (SketchSample s b n) =
      Fintype.card (SketchSample q₁ b n) * Fintype.card (SketchSample q₂ b n) *
        Fintype.card ({t // t ∉ Set.range (Sum.elim f₁ f₂)} → SketchBlock b n) := by
    rw [Fintype.card_congr (blockGroupsEquiv b n f₁ f₂ hg), Fintype.card_prod,
      Fintype.card_prod]
  rw [hsum, hcard, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [← Finset.mul_sum]
  push_cast
  ring

/-- The two restrictions to disjoint block groups are independent and uniform: Fubini for the
pair `(blockRestrict f₁ ω, blockRestrict f₂ ω)`. -/
theorem sketchLaw_expect_blockRestrict_pair {s q₁ q₂ b n : ℕ} (hb : 0 < b)
    (f₁ : Fin q₁ → Fin s) (f₂ : Fin q₂ → Fin s) (hg : Function.Injective (Sum.elim f₁ f₂))
    (G : SketchSample q₁ b n → SketchSample q₂ b n → ℝ) :
    (sketchLaw s b n hb).expect (fun ω => G (blockRestrict f₁ ω) (blockRestrict f₂ ω)) =
      (sketchLaw q₁ b n hb).expect (fun ω₁ =>
        (sketchLaw q₂ b n hb).expect (fun ω₂ => G ω₁ ω₂)) := by
  have h₀ := card_sketchSample_ne_zero (s := s) (n := n) hb
  have h₁ := card_sketchSample_ne_zero (s := q₁) (n := n) hb
  have h₂ := card_sketchSample_ne_zero (s := q₂) (n := n) hb
  have hsum := sum_blockRestrict_pair f₁ f₂ hg G
  simp only [sketchLaw_expect_eq_sum]
  rw [← Finset.sum_div, div_div, div_eq_div_iff h₀ (mul_ne_zero h₂ h₁)]
  linear_combination hsum

/-- Two-stage independence of disjoint block groups: if the first-stage event has probability
`≥ 1 - δ₁` and, for every first-stage outcome in it, the second-stage event has conditional
probability `≥ 1 - δ₂`, then the joint event has probability `≥ 1 - δ₁ - δ₂`. -/
theorem two_stage_independence {s q₁ q₂ b n : ℕ} (hb : 0 < b) (f₁ : Fin q₁ → Fin s)
    (f₂ : Fin q₂ → Fin s) (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂)
    (hdisj : ∀ t₁ t₂, f₁ t₁ ≠ f₂ t₂) (E₁ : SketchSample q₁ b n → Prop)
    (E₂ : SketchSample q₁ b n → SketchSample q₂ b n → Prop) {δ₁ δ₂ : ℝ} (hδ₂ : 0 ≤ δ₂)
    (h₁ : 1 - δ₁ ≤ (sketchLaw q₁ b n hb).prob {ω₁ | E₁ ω₁})
    (h₂ : ∀ ω₁, E₁ ω₁ → 1 - δ₂ ≤ (sketchLaw q₂ b n hb).prob {ω₂ | E₂ ω₁ ω₂}) :
    1 - δ₁ - δ₂ ≤ (sketchLaw s b n hb).prob
      {ω | E₁ (blockRestrict f₁ ω) ∧ E₂ (blockRestrict f₁ ω) (blockRestrict f₂ ω)} := by
  classical
  have hg : Function.Injective (Sum.elim f₁ f₂) := hf₁.sumElim hf₂ hdisj
  -- The joint probability as an iterated expectation over the two groups.
  have hjoint : (sketchLaw s b n hb).prob
      {ω | E₁ (blockRestrict f₁ ω) ∧ E₂ (blockRestrict f₁ ω) (blockRestrict f₂ ω)} =
      (sketchLaw q₁ b n hb).expect (fun ω₁ =>
        FiniteLaw.indicator {ω₁ | E₁ ω₁} ω₁ * (sketchLaw q₂ b n hb).prob {ω₂ | E₂ ω₁ ω₂}) := by
    have key := sketchLaw_expect_blockRestrict_pair hb f₁ f₂ hg
      (fun ω₁ ω₂ => FiniteLaw.indicator {ω₁ | E₁ ω₁} ω₁ *
        FiniteLaw.indicator {ω₂ | E₂ ω₁ ω₂} ω₂)
    have hind : ∀ ω : SketchSample s b n,
        FiniteLaw.indicator
            {ω | E₁ (blockRestrict f₁ ω) ∧ E₂ (blockRestrict f₁ ω) (blockRestrict f₂ ω)} ω =
          FiniteLaw.indicator {ω₁ | E₁ ω₁} (blockRestrict f₁ ω) *
            FiniteLaw.indicator {ω₂ | E₂ (blockRestrict f₁ ω) ω₂} (blockRestrict f₂ ω) := by
      intro ω
      by_cases hA : E₁ (blockRestrict f₁ ω)
      · by_cases hB : E₂ (blockRestrict f₁ ω) (blockRestrict f₂ ω)
        · rw [indicator_of_mem' (show ω ∈ {ω | E₁ (blockRestrict f₁ ω) ∧
              E₂ (blockRestrict f₁ ω) (blockRestrict f₂ ω)} from ⟨hA, hB⟩),
            indicator_of_mem' (show blockRestrict f₁ ω ∈ {ω₁ | E₁ ω₁} from hA),
            indicator_of_mem' (show blockRestrict f₂ ω ∈
              {ω₂ | E₂ (blockRestrict f₁ ω) ω₂} from hB), one_mul]
        · rw [indicator_of_not_mem' (show ω ∉ {ω | E₁ (blockRestrict f₁ ω) ∧
              E₂ (blockRestrict f₁ ω) (blockRestrict f₂ ω)} from fun h => hB h.2),
            indicator_of_not_mem' (show blockRestrict f₂ ω ∉
              {ω₂ | E₂ (blockRestrict f₁ ω) ω₂} from hB), mul_zero]
      · rw [indicator_of_not_mem' (show ω ∉ {ω | E₁ (blockRestrict f₁ ω) ∧
            E₂ (blockRestrict f₁ ω) (blockRestrict f₂ ω)} from fun h => hA h.1),
          indicator_of_not_mem' (show blockRestrict f₁ ω ∉ {ω₁ | E₁ ω₁} from hA), zero_mul]
    rw [FiniteLaw.prob, FiniteLaw.expect_congr _ hind, key]
    apply FiniteLaw.expect_congr
    intro ω₁
    rw [FiniteLaw.prob, FiniteLaw.expect_smul]
  rw [hjoint]
  -- Pointwise lower bound from the second-stage hypothesis.
  have hlow : ∀ ω₁, FiniteLaw.indicator {ω₁ | E₁ ω₁} ω₁ * (1 - δ₂) ≤
      FiniteLaw.indicator {ω₁ | E₁ ω₁} ω₁ * (sketchLaw q₂ b n hb).prob {ω₂ | E₂ ω₁ ω₂} := by
    intro ω₁
    by_cases h : E₁ ω₁
    · rw [indicator_of_mem' (show ω₁ ∈ {ω₁ | E₁ ω₁} from h), one_mul, one_mul]
      exact h₂ ω₁ h
    · rw [indicator_of_not_mem' (show ω₁ ∉ {ω₁ | E₁ ω₁} from h), zero_mul, zero_mul]
  have hmono := (sketchLaw q₁ b n hb).expect_mono hlow
  have hconst : (sketchLaw q₁ b n hb).expect
      (fun ω₁ => FiniteLaw.indicator {ω₁ | E₁ ω₁} ω₁ * (1 - δ₂)) =
      (1 - δ₂) * (sketchLaw q₁ b n hb).prob {ω₁ | E₁ ω₁} := by
    rw [FiniteLaw.prob, ← FiniteLaw.expect_smul]
    apply FiniteLaw.expect_congr
    intro ω₁
    ring
  have hle1 := (sketchLaw q₁ b n hb).prob_le_one {ω₁ | E₁ ω₁}
  nlinarith [mul_nonneg hδ₂ (sub_nonneg.2 hle1)]

/-! ### Head/background conditioning (W-SKETCH) -/

/-- Conditioning on the head: the expectation of `F` equals the average over head configurations
`ω₀` of the conditional expectation `E_ω F (mergeHead I ω₀ ω)`. -/
theorem expect_mergeHead {s b n : ℕ} (hb : 0 < b) (I : Finset (Fin n))
    (F : SketchSample s b n → ℝ) :
    (sketchLaw s b n hb).expect F =
      (sketchLaw s b n hb).expect (fun ω₀ =>
        (sketchLaw s b n hb).expect (fun ω => F (mergeHead I ω₀ ω))) := by
  have hN := card_sketchSample_ne_zero (s := s) (n := n) hb
  -- Swapping the heads of two samples is an involution of pairs of samples.
  have hinv : Function.Involutive (fun p : SketchSample s b n × SketchSample s b n =>
      (mergeHead I p.1 p.2, mergeHead I p.2 p.1)) := by
    rintro ⟨⟨h₀, σ₀⟩, ⟨h, σ⟩⟩
    simp only [mergeHead, Prod.mk.injEq]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> funext t i <;> by_cases hi : i ∈ I <;> simp [hi]
  have hpair : ∑ ω₀ : SketchSample s b n, ∑ ω : SketchSample s b n, F (mergeHead I ω₀ ω) =
      (Fintype.card (SketchSample s b n) : ℝ) * ∑ ω, F ω := by
    calc ∑ ω₀ : SketchSample s b n, ∑ ω : SketchSample s b n, F (mergeHead I ω₀ ω)
        = ∑ p : SketchSample s b n × SketchSample s b n, F (mergeHead I p.1 p.2) :=
          (Fintype.sum_prod_type' (fun ω₀ ω => F (mergeHead I ω₀ ω))).symm
      _ = ∑ p : SketchSample s b n × SketchSample s b n, F p.1 :=
          Fintype.sum_equiv (hinv.toPerm _) _ _ (fun _ => rfl)
      _ = ∑ ω₀ : SketchSample s b n, ∑ _ω : SketchSample s b n, F ω₀ :=
          Fintype.sum_prod_type' (fun ω₀ (_ : SketchSample s b n) => F ω₀)
      _ = (Fintype.card (SketchSample s b n) : ℝ) * ∑ ω, F ω := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [sketchLaw_expect_eq_sum]
  rw [← Finset.sum_div, hpair, mul_div_cancel_left₀ _ hN]

/-- `mergeHead` only depends on the head part of `ω₀`. -/
theorem mergeHead_congr {s b n : ℕ} (I : Finset (Fin n)) (ω₀ ω₀' ω : SketchSample s b n)
    (h₁ : ∀ t, ∀ i ∈ I, ω₀.1 t i = ω₀'.1 t i) (h₂ : ∀ t, ∀ i ∈ I, ω₀.2 t i = ω₀'.2 t i) :
    mergeHead I ω₀ ω = mergeHead I ω₀' ω := by
  simp only [mergeHead, Prod.mk.injEq]
  constructor
  · funext t i
    by_cases hi : i ∈ I
    · rw [if_pos hi, if_pos hi]
      exact h₁ t i hi
    · rw [if_neg hi, if_neg hi]
  · funext t i
    by_cases hi : i ∈ I
    · rw [if_pos hi, if_pos hi]
      exact h₂ t i hi
    · rw [if_neg hi, if_neg hi]

end SparseStack
