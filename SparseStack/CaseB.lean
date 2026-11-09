import SparseStack.Localization
import SparseStack.Linearization
import SparseStack.HeadRepair
import SparseStack.Numerics.CaseBParams
import SparseStack.CaseBLinalg

/-!
# Case B of `prop:parameters` (method D): `L ≥ 64` and `ζ < 104 L` (paper, lines 1238–1330)

`q = ⌊ζ/2⌋`; the first two disjoint `q`-block groups `X` (blocks `0..q-1`) and `Y` (blocks
`q..2q-1`), each normalized by `q^{-1/2}`. With `κ = 1`, `R = max{r, 8m} = r`.
1. localization on `X` (failure `≤ 3/20000`), then `certificate` gives `I`, `|I| ≤ 8m`, with
   `∑_{i∉I} (Qx)_i² ≤ u‖x‖² + v‖Xx‖²`;
2. background basis `Q_J = V B_J` (`V` isometry supported off `I`, `d ≤ r`);
3. head repair on `Y` for `(I, V)`, conditionally on group 1 (failure `≤ 997/20000`):
   `β‖h‖² ≤ ‖Y(h + Vf)‖² + t₀‖f‖²`, with `h = E_I Q x`, `f = B_J x`;
4. combine: `YᵀY + γ H_J ⪰ β I`, `H_J ⪯ u I + v XᵀX`, `γ v ≥ 1`, group inequality
   `AᵀA ⪰ ρ₀ (XᵀX + YᵀY)`, so `AᵀA ⪰ (ρ₀/v)(β/γ - u) I = α I`;
5. total failure `3/20000 + 997/20000 = 1/20`.
-/

namespace SparseStack

open SparseFock

private theorem sqNorm_nonneg' {ι : Type} [Fintype ι] (v : ι → ℝ) : 0 ≤ sqNorm v := by
  unfold sqNorm dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

/-- Case B: the probability clause (Rayleigh form) when `L ≥ 64` and `ζ < 104 L`. -/
theorem caseB {n r : ℕ} (hr : 2 ≤ r) (hrn : r ≤ n) (Q : Matrix (Fin n) (Fin r) ℝ)
    (hQ : Q.transpose * Q = 1) (hL : 64 ≤ logER r)
    (hζ : (numBlocks r : ℝ) < 104 * logER r) :
    (19 / 20 : ℝ) ≤ uniformProb (SketchSample (numBlocks r) (numBuckets r) n)
      (fun ω => QuadraticLowerBound (sketchMatrix ω * Q) constAlpha) := by
  classical
  obtain ⟨hr11, hq1, hqr, hθ, hm1, hm8, hm16, hqC, hqreg, hbq, hρ⟩ := caseB_params hr hL hζ
  have hb : 0 < numBuckets r := lt_of_lt_of_le (by norm_num) (two_le_numBuckets hr)
  set ζ := numBlocks r with hζdef
  set b := numBuckets r with hbdef
  set q := ζ / 2 with hqdef
  set m := locWidth r q with hmdef
  have h2q : q + q ≤ ζ := by omega
  -- the two disjoint block groups `0..q-1` and `q..2q-1`
  let f₁ : Fin q → Fin ζ := fun t => ⟨t.1, by have := t.2; omega⟩
  let f₂ : Fin q → Fin ζ := fun t => ⟨q + t.1, by have := t.2; omega⟩
  have hf₁ : Function.Injective f₁ := by
    intro a c h
    have := congrArg Fin.val h
    exact Fin.ext this
  have hf₂ : Function.Injective f₂ := by
    intro a c h
    have := congrArg Fin.val h
    simp only [f₂] at this
    exact Fin.ext (by omega)
  have hdisj : ∀ t₁ t₂, f₁ t₁ ≠ f₂ t₂ := by
    intro t₁ t₂ h
    have := congrArg Fin.val h
    simp only [f₁, f₂] at this
    have := t₁.2
    omega
  -- stage 1: localization on the first group
  let E₁ : SketchSample q b n → Prop := fun ω₁ =>
    ∀ x : Fin r → ℝ, sqNorm x = 1 → 1 / 9 ≤ distSparseSq m (Q.mulVec x) →
      lambdaSq ≤ sqNorm ((sketchMatrix ω₁ * Q).mulVec x)
  have hE₁ : 1 - 3 / 20000 ≤ (sketchLaw q b n hb).prob {ω₁ | E₁ ω₁} := by
    have hloc := localization hr11 hq1 hqr hb hθ Q hQ
    apply one_sub_le_prob_of_prob_compl_le
    refine le_trans (FiniteLaw.prob_mono _ ?_) hloc
    intro ω₁ hω₁
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, E₁] at hω₁ ⊢
    push Not at hω₁
    exact hω₁
  -- certificate: a coordinate set for every localization success (a function of group 1 only)
  have hcertE : ∀ ω₁, E₁ ω₁ → ∃ I : Finset (Fin n), I.card ≤ 8 * m ∧
      ∀ x, ∑ i ∈ Iᶜ, (Q.mulVec x i) ^ 2 ≤
        uCert * sqNorm x + vCert * sqNorm ((sketchMatrix ω₁ * Q).mulVec x) :=
    fun ω₁ h => certificate hm1 Q hQ (sketchMatrix ω₁ * Q) h
  let Isel : SketchSample q b n → Finset (Fin n) := fun ω₁ =>
    if h : E₁ ω₁ then Classical.choose (hcertE ω₁ h) else ∅
  have hIsel : ∀ ω₁ (h : E₁ ω₁), (Isel ω₁).card ≤ 8 * m ∧
      ∀ x, ∑ i ∈ (Isel ω₁)ᶜ, (Q.mulVec x i) ^ 2 ≤
        uCert * sqNorm x + vCert * sqNorm ((sketchMatrix ω₁ * Q).mulVec x) := by
    intro ω₁ h
    have hI : Isel ω₁ = Classical.choose (hcertE ω₁ h) := dif_pos h
    rw [hI]
    exact Classical.choose_spec (hcertE ω₁ h)
  -- background bases, chosen in advance for every coordinate set
  have hbas := fun I : Finset (Fin n) => background_basis Q I
  choose dsel Vsel Bsel hBsel using hbas
  -- stage 2: head repair on the second group, for the selected head and background
  let E₂ : SketchSample q b n → SketchSample q b n → Prop := fun ω₁ ω₂ =>
    ∀ h : Fin n → ℝ, (∀ i, i ∉ Isel ω₁ → h i = 0) → ∀ f : Fin (dsel (Isel ω₁)) → ℝ,
      betaRep * sqNorm h ≤
        sqNorm ((sketchMatrix ω₂).mulVec (h + (Vsel (Isel ω₁)).mulVec f)) + t0 * sqNorm f
  have hE₂ : ∀ ω₁, E₁ ω₁ → 1 - 997 / 20000 ≤ (sketchLaw q b n hb).prob {ω₂ | E₂ ω₁ ω₂} := by
    intro ω₁ h₁
    obtain ⟨hcard, -⟩ := hIsel ω₁ h₁
    obtain ⟨hd, hV, hVs, -⟩ := hBsel (Isel ω₁)
    exact head_repair hr hb hqC hqreg hbq (Isel ω₁) (by omega) (by omega) (Vsel (Isel ω₁)) hV
      hVs hd
  have h2 := two_stage_independence hb f₁ f₂ hf₁ hf₂ hdisj E₁ E₂
    (by norm_num : (0 : ℝ) ≤ 997 / 20000) hE₁ hE₂
  -- the joint event implies the Rayleigh lower bound
  rw [uniformProb_eq_prob hb]
  refine le_trans (by norm_num : (19 / 20 : ℝ) ≤ 1 - 3 / 20000 - 997 / 20000)
    (le_trans h2 (FiniteLaw.prob_mono _ ?_))
  rintro ω ⟨h₁, h₂⟩
  obtain ⟨-, hcert⟩ := hIsel (blockRestrict f₁ ω) h₁
  obtain ⟨-, hV, -, hBJ⟩ := hBsel (Isel (blockRestrict f₁ ω))
  have key := caseB_combine Q hQ (Isel (blockRestrict f₁ ω)) (Vsel (Isel (blockRestrict f₁ ω))) hV
    (Bsel (Isel (blockRestrict f₁ ω))) hBJ
    (fun v => sqNorm ((sketchMatrix (blockRestrict f₁ ω)).mulVec v))
    (fun v => sqNorm ((sketchMatrix (blockRestrict f₂ ω)).mulVec v))
    (fun v => sqNorm ((sketchMatrix ω).mulVec v)) ((q : ℝ) / ζ) hρ
    (fun v => sqNorm_sketch_ge_groups f₁ f₂ hf₁ hf₂ hdisj ω v)
    (fun x => by
      have := hcert x
      rwa [← Matrix.mulVec_mulVec] at this)
    h₂ (fun v => sqNorm_nonneg' _) (fun v => sqNorm_nonneg' _)
  show QuadraticLowerBound (sketchMatrix ω * Q) constAlpha
  intro x
  have hx := key x
  rw [← Matrix.mulVec_mulVec]
  exact hx

end SparseStack
