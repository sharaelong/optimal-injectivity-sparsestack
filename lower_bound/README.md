# Optimal Injectivity of the SparseStack — Complete Lean 4.33.1 Formalization

Complete, dual-kernel certified Lean `v4.33.1` formalization of all 10 sections (pp. 1–50: Upper Bound Sections 1–7 and Lower Bound Sections 8–10; 35 individual `Prop` statements + `AllPaperTheorems` = 36 certified theorems) of *"Optimal Injectivity of the SparseStack"*.

## Toolchain & Dependency Pins

- **Lean Toolchain (`lean-toolchain`):** `leanprover/lean4:v4.33.1`
- **Mathlib (`lake-manifest.json`):** `0df444a360eaa60ab8c11dca51a86af692955474`
- **Specification Lock (`SPEC_LOCK.sha256`):** `Osi/Spec.lean` SHA-256 `82291b61952608c38e273bd8c0cafc4ec04612cda896fad351bceebf3127357e`
- **Axioms (`#print axioms Osi.Headline.allPaperTheorems`):** `[propext, Classical.choice, Quot.sound]` (`0 sorry`, `0` custom axioms, `0` warnings)

## Quick Start

```bash
unzip osi_lean4_v4331.zip
cd osi_lean4_v4331
lake exe cache get
lake build Osi.Headline Osi.GateCheck
```

## Key Directories & Files

- `Osi/Spec.lean` — Mathlib-only formal statements of all 35 paper theorems, propositions, and lemmas + `AllPaperTheorems`.
- `Osi/Headline.lean` — Proofs of all 36 `Osi.Spec.*` theorems with literal `Osi.Spec` types.
- `Osi/Prelim/` — `SubspaceSing.lean`, `Hypergeom.lean`.
- `Osi/UpperBound/` — `Sec234.lean`, `OverlapProp.lean`, `Sec5.lean`, `Sec6.lean`, `GeneralParams.lean` (Sections 1–7).
- `Osi/LowerBound/` — `RowPreprocess.lean`, `C4Subgraph.lean`, `TreeCancel.lean`, `TuranCenters.lean`, `HallReservoirs.lean`, `CoordReduction.lean`, `Endgame.lean` (Sections 8–10).
- `Osi/Gate.lean` & `Osi/GateCheck.lean` — Elaborated cone & module trust-gate auditor (`58,736` constants in the 36-root `Osi.Headline` cone; `65,714` constants across all `126` project modules).
- `SparseStack/` & `vendor/heidary_formal/` — Zero-axiom supporting probability, concentration, and matrix moment libraries.
- `STATEMENT_REVIEW.md` & `BLUEPRINT.md` — Paper-to-Lean statement audit and module dependency blueprint.
- `OsiChallenge/Challenge.lean`, `OsiChallenge/Solution.lean`, `comparator_config.json` — Standalone `leanprover/comparator` verification target & solution.
