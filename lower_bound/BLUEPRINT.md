# BLUEPRINT: *Optimal Injectivity of the SparseStack* (Complete Sections 1–10)

## 1. Module Dependency DAG

```text
Osi/Spec.lean   (Mathlib-only specification: 35 Prop statements + AllPaperTheorems; 0 sorry)
  │
  ├── Osi/Prelim/SubspaceSing.lean   [Wave 1: Rayleigh/eigenvalue iff, coordFrame, measurability,
  │                                    SparseStack measure/mean/sparsity bridges, Theorem 1.3 necessity]
  ├── Osi/Prelim/Hypergeom.lean      [Wave 1: uniformSubsetProb algebra, without-replacement avoidance,
  │                                    hypergeometric Chebyshev, 2-stage subsampling, disjoint capture]
  ├── Osi/LowerBound/TreeCancel.lean [Wave 1: Lemma 9.1 star cancellation + Lemma 9.2 greedy leaves]
  ├── Osi/LowerBound/TuranCenters.lean [Wave 1: Lemma 9.3 Caro–Wei + Lemma 9.4 virtual splitting & centers]
  │
  ├── Osi/LowerBound/RowPreprocess.lean [Wave 2: Lemma 8.1 heavy rows + Lemma 8.2 small/1-sparse elim]
  │     (imports SubspaceSing, Hypergeom)
  ├── Osi/LowerBound/C4Subgraph.lean    [Wave 2: c4Free_card_le_pairs + Lemma 8.3 C4-free subgraph G₀]
  │     (imports Hypergeom)
  ├── Osi/LowerBound/HallReservoirs.lean [Wave 2: Lemma 9.5 Hall + Lemma 9.6 reservoirs + Theorem 9.7 forest]
  │     (imports C4Subgraph, TreeCancel, TuranCenters)
  ├── Osi/LowerBound/CoordReduction.lean [Wave 2: Lemma 10.1 coordinate-subspace minimax reduction]
  │     (imports SubspaceSing, Hypergeom)
  ├── Osi/UpperBound/OverlapProp.lean    [Wave 2: Proposition_SparseStack_Overlap (η = 5 ζ⁴ / (2 k))]
  │     (imports SubspaceSing)
  ├── Osi/UpperBound/Sec234.lean         [Wave 2: Lemmas 3.2, 3.3, 3.4, Theorem 2.1, Lemmas 4.1, 4.2, Theorem 2.2]
  │     (imports Osi.Spec, SparseStack.{SmallBall,Rounding,Localization,Linearization,Prob.Tails})
  ├── Osi/UpperBound/Sec5.lean           [Wave 2: Lemmas 5.3, 5.4, 5.5]
  │     (imports SubspaceSing, SparseStack.{IidNorm,CrossGram,External.StackMoment})
  │
  ├── Osi/LowerBound/Endgame.lean        [Wave 3: Theorem 10.2 + Theorem 1.3 (HalfProb, 19/20, QuadraticN)]
  │     (imports SubspaceSing, Hypergeom, RowPreprocess, C4Subgraph, HallReservoirs, CoordReduction)
  ├── Osi/UpperBound/Sec6.lean           [Wave 3: Lemmas 6.1, 6.2 (c₁=1/1152), 6.3, Theorem 2.3]
  │     (imports SubspaceSing, Sec5, SparseStack.{HeadRepair,Repair.Assembly,Repair.Retention})
  │
  ├── Osi/UpperBound/GeneralParams.lean  [Wave 4: Theorem 1.1 (Schedule, GeneralParams, PaperRange) +
  │                                        Theorem_Optimal_SparseStack_Tightness]
  │     (imports SubspaceSing, OverlapProp, Endgame, SparseStack.{Main,CaseA,CaseB})
  │
  └── Osi/Headline.lean                  [0 sorry: proves all 35 Osi.Spec.* Props + AllPaperTheorems]
        │
        └── Osi/GateCheck.lean           [G1 trust gate on Osi + SparseStack + SparseFockFormal]
```

## 2. Parallel Leaf Proving Units, Status, & Proof Strategies

| Unit | File | Paper Targets | Status | Key Mathematical Strategy |
|---|---|---|---|---|
| **U1** | `Osi/Prelim/SubspaceSing.lean` | Prelim + `Theorem_1_3_NecessityOfAmbientBound` | **PASS (`0 sorry`, `lc=True`)** | Spectral theorem (`Matrix.IsHermitian.eigenvectorBasis`) ↔ Rayleigh quotient; `coordFrame` orthonormal columns; `IsRandomMatrix` measurability of `frobSq`, `rowSupport`, `SatisfiesOverlapCond`, and `MinEigenvalueAtLeast` (countable intersection over `q : Fin r → ℚ`); `DiscreteMeasurableSpace` + `SparseStack.Sketch.Mean` bridges; `Ω = I_n` on `PUnit`. |
| **U2** | `Osi/Prelim/Hypergeom.lean` | Section 8 & 10 hypergeometric toolkit | **PASS (`0 sorry`, `lc=True`)** | `powersetCard` counting identities; `C(n - |A|, r) / C(n, r) ≤ (1 - |A|/n)^r`; hypergeometric second factorial moment `E[X(X-1)] = |B|(|B|-1) n₀(n₀-1)/(n(n-1))` ⇒ `Var(X) ≤ E[X]`; `C(n, n₀) C(n₀, r) = C(n, r) C(n - r, n₀ - r)` double-counting; negative correlation `E[1_{T_s ⊆ R} 1_{T_u ⊆ R}] = C(n₀ - 2B, r - 2B)/C(n₀, r) ≤ p²` ⇒ `Pr(N_cap = 0) ≤ 1 / (T p)`. |
| **U3** | `Osi/LowerBound/RowPreprocess.lean` | `Lemma 8.1`, `Lemma 8.2` | **PASS (`0 sorry`, `lc=True`)** | `160 |I_heavy| ≤ frobSq S ≤ 10 n`; Case 1 (`|I_small| ≥ n/16`): `uniformSubsetProb_disjoint_le` gives `(15/16)^r ≤ 1/10`, unit coordinate vector breaks `MinEigenvalueAtLeast`; Case 2 (`|I_one| ≥ n/16`): two-stage subsampling (`n₀ = ⌊64 K r⌋₊`) + `disjoint_subsets_capture_chebyshev` on disjoint 2-row pairs inside heavy column buckets yields same-column collision w.p. `≥ 9/10`, 2-sparse cancellation gives `S_Rᵀ x = 0`. |
| **U4** | `Osi/LowerBound/C4Subgraph.lean` | `c4Free_card_le_pairs`, `Lemma 8.3` | **PASS (`0 sorry`, `lc=True`)** | 2-element subset injection into `powersetCard 2 (Fin k)`; `uniformSubsetProb_inter_card_chebyshev` bounds `Pr(|V₀ \ V_clean| > n₀/4) ≤ 1/16` (`C_samp₀ ≥ 48`) and `uniformSubsetProb_pairs_markov` bounds `Pr(|subCollidingPairs| > n₀/16) ≤ 1/16`; `prunedRows` deletes `≤ n₀/4 + n₀/16 < 3 n₀/8` rows and eliminates all `u < v` 4-cycles. |
| **U5** | `Osi/LowerBound/TreeCancel.lean` | `Lemma 9.1`, `Lemma 9.2` | **PASS (`0 sorry`, `lc=True`)** | `C₄`-freeness ensures each leaf `ℓ ∈ L j₁` has `S_{ℓ, j₂} = 0` for `j₂ ∈ supp(s_{i*}) \ {j₁}`, giving exact cancellation on `supp(s_{i*})`; Cauchy–Schwarz on each outer column `c` (hit by `≤ 1` leaf via disjoint outer supports) + `w_{ℓ,j} ≥ w_{i*,j}` gives `∑_{c ∉ supp(s_{i*})} (Sᵀ x)_c² ≤ d ‖s_{i*}‖² / q`. Greedy selection across `≤ ζ` branches blocks `≤ (ζ - 1)²` candidates per chosen leaf. |
| **U6** | `Osi/LowerBound/TuranCenters.lean` | `Lemma 9.3`, `Lemma 9.4` | **PASS (`0 sorry`, `lc=True`)** | Caro–Wei greedy min-degree neighborhood deletion `|I| ≥ m / (1 + d_avg)`; virtual-column chunking into blocks of size `≤ Δ = ⌈ζ n₀ / k⌉` creates `≤ k + n₀ ζ / Δ ≤ 2 k` virtual columns; `|J_elig| ≥ |V_G0| - 2 k D ≥ n₀ / 2`, conflict edges `≤ k' Δ² / 2`, Caro–Wei yields `|I_center| ≥ c_T r / ζ⁵`. |
| **U7** | `Osi/LowerBound/HallReservoirs.lean` | `Lemma 9.5`, `Lemma 9.6`, `Theorem 9.7` | **PASS (`0 sorry`, `lc=True`)** | Mathlib `Finset.all_card_le_biUnion_card_iff_exists_injective'` proves `Lemma 9.5`; cloning `J_branch × Fin L` and double-counting edges `D |A| ≤ ζ L |N(A)|` proves `Lemma 9.6`; `c4Free_card_le_pairs` forces `16 ζ⁶ ≤ r` (`T = ⌈c_T r / ζ⁵⌉ ≥ 1`), `Lemma 9.4` + `Lemma 9.6` + `Lemma 9.2` + `Lemma 9.1` build `T` disjoint witness sets of exact padded size `1 + ζ q` in `V_G0`. |
| **U8** | `Osi/LowerBound/CoordReduction.lean` | `Lemma 10.1` | **PASS (`0 sorry`, `lc=True`)** | `expected_frobSq_of_isIsotropic` + Markov gives `P(frobSq ≤ 10 n) ≥ 9/10`; union with `SatisfiesOverlapWhp` (`≥ 9/10`) gives good event `E` with `P(E) ≥ 4/5`; finite sum interchange over `R ∈ univ.powersetCard r` bounds `min_R P(σ_min ≥ α) ≤ (4/5)(1/4) + 1/5 = 9/20 < p_osi`. |
| **U9** | `Osi/LowerBound/Endgame.lean` | `Theorem 10.2`, `Theorem 1.3` (3 forms) | **PASS (`0 sorry`, `lc=True`)** | If `|I_small| ≥ n/16` or `|I_one| ≥ n/16`, `Lemma 8.2` gives `Pr(σ_min ≥ α) ≤ 1/10 ≤ 1/4`; else `|V_clean| ≥ 13 n/16`, two-stage subsampling (`Lemma 8.3` w.p. `≥ 7/8` + `Theorem 9.7` + `disjoint_subsets_capture_chebyshev` `≤ 1/8` when `ζ ≤ c √(log r / log log r)`) gives `Pr(σ_min ≥ α) ≤ 1/4`; `k < r` gives rank deficiency (`σ_min = 0 < α`); combine with `Lemma 10.1`. |
| **U10** | `Osi/UpperBound/OverlapProp.lean` | `Proposition_SparseStack_Overlap` | **PASS (`0 sorry`, `lc=True`)** | Exact fiber bijection `doubleCollEquiv` over `SketchSample ζ b n` proves `4 b² ∑_ω overlapPairCount ≤ ζ² n² |Ω|`; Markov's inequality with `η = 5 ζ⁴ / (2 k)` yields `Pr(overlapPairCount ≤ η n² / k) ≥ 9/10`. |
| **U11** | `Osi/UpperBound/Sec234.lean` | `Lemmas 3.2–3.4`, `Thm 2.1`, `Lemmas 4.1–4.2`, `Thm 2.2` | **PASS (`0 sorry`, `lc=True`)** | Generalize `SparseStack.{SmallBall,Rounding,Localization,Linearization}` to arbitrary `ε, δ_loc ∈ (0, 1)` and general `MeasureTheory.IsProbabilityMeasure P`. |
| **U12** | `Osi/UpperBound/Sec5.lean` | `Lemmas 5.3, 5.4, 5.5` | **PASS (`0 sorry`, `lc=True`)** | Bridge `SparseStack.{IidNorm,CrossGram,External.StackMoment}` (`spectralNorm` = L2 operator norm via `Matrix.l2_opNorm_def`) to general `p ≥ max{1, log(2 d)}` and `I = ∅` / `d = 0` base cases. |
| **U13** | `Osi/UpperBound/Sec6.lean` | `Lemmas 6.1, 6.2, 6.3`, `Theorem 2.3` | **PASS (`0 sorry`, `lc=True`)** | Prove `Lemma 6.2(i)` at exact `c₁ = 1/1152` via independent-block MGF Markov (`base = 5/4`) + `Lemma 6.2(ii)` union bound; generalize `SparseStack.HeadRepair` to arbitrary `t₀ ∈ (0, 1/4)`, `δ_rep ∈ (0, 1)`, `H₀ > 0`, combining Case 1 (`Lemma 5.5`) and Case 2 (`Lemma 6.1 + Lemma 6.2`), plus `I = ∅`. |
| **U14** | `Osi/UpperBound/GeneralParams.lean` | `Theorem 1.1` (3 forms) + `Theorem_Optimal_SparseStack_Tightness` | **PASS (`0 sorry`, `lc=True`)** | Lift `SparseStack.CaseA` and `SparseStack.CaseB` to arbitrary integer `(ζ, b)` with `ζ ≥ C √log(e r), b ≥ 2, ζ b ≥ K r`, bridge via `SubspaceSing`, and pair with `OverlapProp` + `Theorem_1_3_QuadraticN` (`C_H ≥ 5/2`). |
