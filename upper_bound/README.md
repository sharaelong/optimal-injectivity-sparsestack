# Optimal Injectivity of the SparseStack — Lean 4 (`v4.33.1`) Upper-Bound Formalization

Complete machine-checked Lean 4 (`leanprover/lean4:v4.33.1`) formalization of the **Upper-Bound side (Sections 1–7, pp. 1–40)** of *"Optimal Injectivity of the SparseStack"* (`constant_injectivity_sparsestack-2.pdf`), covering all **28** mathematical statements (theorems, propositions, lemmas, claims, and facts) plus their top-level conjunction `AllUpperBoundTheorems` (**29 certified theorems**), with `0` `sorry`s, `0` custom axioms (`{propext, Classical.choice, Quot.sound}` only), and `0` compiler warnings.

---

## Quick Start (Build & Kernel Replay)

Prerequisite: [`elan`](https://github.com/leanprover/elan) (which automatically selects `leanprover/lean4:v4.33.1` from `lean-toolchain`).

```bash
# 1. Unpack archive and enter repository
tar -xzf osi_ub_v2_lean.tar.gz
cd osi_ub_v2

# 2. Fetch pinned dependencies and precompiled Mathlib cache
lake exe cache get

# 3. Compile all 29 upper-bound theorems and run the Lean-kernel trust gate
lake build OsiUb OsiUb.GateCheck

# 4. (Optional) Run full static + SHA-256 + elaborated gate script
bash scripts/gate.sh

# 5. (Optional) Replay all declarations from scratch in Lean's standalone kernel checker
lake env leanchecker --fresh OsiUb.Headline
```

---

## Repository Layout (`145` `.lean` files)

- **`OsiUb/Spec.lean`** (`1,104` lines, `63,797` bytes, SHA-256 `fac86a78b27ec315857b605fc4553f85823b9aab9a622cca5100205f101985c7`):
  Self-contained specification importing `Mathlib` only. Defines the finite SparseStack probability space (`sparseStackOmega`, `sparseStackMeasure`), `IsRandomMatrix`, `IsIsotropic`, `IsRowSparse`, `IsOSI`, `SatisfiesOverlapWhp`, `MinEigenvalueAtLeast`, `distSparse`, `IsFlatVec`, `spectralNorm`, `LoewnerLe`, conditional isolation/cross-Gram operators, and the exact `Prop` statements of all 28 upper-bound results plus `AllUpperBoundTheorems`.
- **`OsiUb/Headline.lean`**:
  Exports the 29 top-level certified theorems (`theorem_1_1_GeneralParams`, `theorem_1_1_PaperRange`, `theorem_1_1_Schedule`, `proposition_SparseStack_Overlap`, ..., `allUpperBoundTheorems`), each ascribed directly to its corresponding `Prop` in `OsiUb/Spec.lean`.
- **`OsiUb/Prelim/SubspaceSing.lean`**:
  Subspace singular-value, Rayleigh-quotient, and Loewner-order preliminaries (Section 1.4).
- **`OsiUb/UpperBound/`**:
  - `OverlapProp.lean` — Definition 1.2 & SparseStack Overlap Proposition (Section 1.2).
  - `GeneralParams.lean` — Theorem 1.1 across general $(\zeta, b)$ parameters, literal paper window, and linear-size schedule (Sections 1.2 & 7).
  - `Sec234.lean` — Theorem 2.2, Theorem 2.3, Fact 3.1 (McDiarmid), Lemma 3.2, Lemma 3.3, Lemma 4.1, Lemma 4.2, and Claim 4.3 (Sections 2–4).
  - `Sec5.lean` — Lemma 2.4 (ambient and disjoint-submatrix forms), Fact 5.1, Fact 5.2, Lemma 5.3, Claim 5.4, Lemma 5.5, Claim 5.6, and Lemma 5.7 (Section 5).
  - `Sec6.lean` — Definitions 6.1–6.2 equivalence, Lemma 6.3 (unconditional and conditional), Lemma 6.4(i)–(ii) at exact $c_1 = 1/2304$, and Theorem 2.5 (all integer $\zeta$ plus literal $\beta = 11/24 - t_0$ for even $\zeta$) (Section 6).
- **`SparseStack/`** (`70` `.lean` files):
  Core measure-theoretic, concentration, Sion minimax, coupling/convex-order, balls-into-bins isolation, and operator-norm proof libraries.
- **`vendor/heidary_formal/`** (`56` `.lean` files):
  Pinned external MIT-licensed `SparseFockFormal` formalization (`[Hei26]`) used to prove `Fact_5_1_HeidaryOffDiagMoment` without custom axioms.
- **`OsiUb/Gate.lean`, `OsiUb/GateCheck.lean`, `scripts/gate.sh`**:
  Environment-cone audit verifying that all 29 theorems depend only on `{propext, Classical.choice, Quot.sound}`, with zero `sorryAx`, zero `native_decide` / compiler-trust axioms, and zero `unsafe` / `@[implemented_by]` / `@[extern]` project declarations.
- **`STATEMENT_REVIEW.md`**:
  Detailed mathematical review of Sections 1–7 against the manuscript, documenting proof subtleties (e.g., Lemma 6.4(i) McDiarmid granularity, Lemma 6.3 high-$\zeta$ split via Lemma 5.7, scalar-variance Matrix Bernstein sufficiency) and minor camera-ready typo fixes.
- **`kit/`**:
  Standalone `comparator` (`leanprover/comparator`) + `nanoda_bin` + `con-leche --verified` adversarial verification kit (`OsiUbChallenge/Challenge.lean`, `OsiUbChallenge/Solution.lean`, `comparator_config.json`, 6 negative controls `Neg1`–`Neg6`, `SHA256SUMS`, and helper scripts; see `kit/RED_TEAM_BRIEF.md`).
