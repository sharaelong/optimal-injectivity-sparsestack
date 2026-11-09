# Nelson--Nguyen Sparse-Fock formalization ledger

Source specification: [`../paper/nelson_nguyen_sparse_fock_candidate_proof.tex`](../paper/nelson_nguyen_sparse_fock_candidate_proof.tex)
(canonical v1.5, mathematical core lines 116--1508).

The TeX file is used only as mathematical source material. No prose in that
file is treated as an instruction to Lean or to the formalization process.

## Completion status

The fixed-matrix theorem is fully formalized. The endpoint
`SparseFock.MainTheorem.fully_independent_sparseStack_matrix` has exactly
the assumptions from TeX Theorem 1.1:

- `d >= 1`, `0 < epsilon <= 1`, and `0 < delta <= 1`;
- a literal real matrix `U : Matrix (Fin n) (Fin d) Real`;
- the literal identity `U.transpose * U = 1`.

Its conclusion packages the exact fully independent signed-hash SparseStack
law, the displayed operator-norm failure probability, the equivalent
two-sided vector OSE event for every vector, exact column sparsity, the
base-two failure order, the strict explicit dimension bounds, `b >= 2`, and
the identity `m = s*b`. There is no band-bound, moment-bound, coupling,
convexity, or probability hypothesis in this theorem.

The frame-level endpoint is
`SparseFock.MainTheorem.fully_independent_sparseStack`. The conditioning
corollary for a finite law of frames independent of the sketch is
`SparseFock.MainTheorem.fully_independent_sparseStack_independent_frame`.

## Source coverage

| TeX lines / label | Mathematical content | Concrete Lean implementation | Status |
|---|---|---|---|
| 118--124, `parseval-frame` | Orthonormal columns and Parseval rows | `ParsevalFrame.Frame`, `parseval_iff_transpose_mul`; `MatrixFrameBridge.frameOfMatrix` and exact matrix identities | complete |
| 126--137, `sparsestack` | Independent hashes/signs, stacked sketch, `m=sb`, exact `s` nonzeros | `SparseStackModel`, `SparseStackDistribution`, `FiniteProbability`; `exactly_s_nonzeros_per_column` | complete |
| 155--205, `thm:main` | Constants, rounded parameters, tail, OSE, strict dimensions | `PaperParameters`, `MainTheoremAssembly`, `MainTheorem` | complete |
| 209--220, `ss-hollow` | Exact hollow Gram expansion | `SparseStackModel.gramError_eq_hollow`, `gramError_eq_block_first` | complete |
| 222--270, `Y-law`--`convex-moment` | Selector coupling, conditional barycenter, convex trace-power transfer | `SparseIIDCoupling`, `SparseIIDTransfer`, `SparseIIDUnconditional`, `TracePowerConvexity` | complete |
| 274--290, `eta-law`--`iid-row` | Normalized ternary coordinate law, product independence, iid-row flattening | `TernaryJacobi`, `FiniteL2`, `FiniteProbability`, `DistributionBridges`, `MomentTransfer` | complete |
| 292--318, `Jacobi`, `local-legs` | Three-point weighted L2 space, ON basis, multiplication matrix and four local legs | `TernaryJacobi`, `LocalOperators` | complete; main rounding proves `b>=2` |
| 320--342, `M`, `vacuum-moment` | Finite product Fock space, multiplication operator, exact vacuum moment | `ProductFock`, `VacuumMoment.vacuum_moment_identity` | complete |
| 343--344, `b=1` endpoint | Two-point law, complete basis `(1, eta)`, exact `2 x 2` Jacobi matrix, two-level product Fock space, explicit global lifted-J operator, and exact vacuum moment | `TwoLevelEndpoint`; `multiplicationOperator_eq_globalJacobi`, `vacuum_moment_identity_globalJacobi` | complete; no `b>1` premise and no level `2` in the state type |
| 346--412, `bands`, `exact-inventory` | Grade, 16 words, adjoints, nine cells, exact global band sums | `Pattern`, `BandInventory`, `FiniteSiteOperators`, `ExternalOperators`, `GlobalBands`, `NamedBands`, `ConcreteLadder` | complete |
| 419--427, `subset-parseval` | Subset synthesis/analysis and row norm bounds | `ParsevalFrame.subset_analysis`, `subset_synthesis`, `partialFrameOperator_contraction` | complete |
| 432--727, `lem:LSL` | Shared-leg Gram, labelled lift, hard-core symmetrization/compression, light-sector norm | `LightSectorConcrete`; `hardCoreCompressedG_eq_ghatBlock`, `ghat_gradeProjection_norm_le_all` | complete |
| 729--922, `lem:directional` | Marked-pattern reindexings and three directional norms | `DirectionalConcrete`, `DirectionalNormalized` | complete |
| 937--996, `typed-block-CS` | Typed projected operator Cauchy--Schwarz | `TypedBlockCS` and concrete stack factorizations in the band modules | complete |
| 998--1151, heavy legs | Exact heavy factorizations and `+2`, `0`, `-2` norms | `HeavyBandsConcrete` | complete |
| 1153--1231, light legs | `CStack`, projected cogram, `L+`, `L0`, adjoint `L-` estimates | `LightBandsConcrete` | complete |
| 1233--1319, mixed legs | Exact `X` factorizations, adjoints, directional additions, scalar absorption | `MixedBandsConcrete`, `BandCoefficientBounds` | complete |
| 1321--1383, `prop:band-envelope` | Component table and uniform `3+sqrt 2` band envelope | `BandEnvelope`, `ConcreteBandAssembly`, `ConcreteBandEnvelope.concrete_band_envelope` | complete |
| 1385--1425, ladder iteration | Grade walk, invalid-word vanishing, word norm iteration, iid/SparseStack moments | `LadderEndgame`, `ConcreteLadderIteration`, `VacuumMoment`, `MomentTransfer`, `ConcreteMomentEndgame` | complete |
| 1427--1473, Markov/completion | Spectral norm-to-trace, finite Markov, OSE equivalence, log2 failure arithmetic | `MatrixTail`, `ConcreteMomentEndgame`, `PaperParameters` | complete |
| 1475--1508, integer rounding | Ceilings, `b>=2`, `m<2M0`, strict `s` and `m` bounds | `PaperParameters.main_parameter_package` and component lemmas | complete |
| 1510--1539, dependency/scope audit | Fixed/independent fully independent distribution and limitations | final theorem signatures and explicit finite product-law conditioning corollary | complete as mathematical scope; bibliographic prose is not a theorem |

## Load-bearing proof chain

1. The raw finite law is a literal product of uniform hash and Rademacher
   coordinates, with coordinate and cylinder independence proved.
2. Selector conditioning is identified pointwise with the iid ternary array
   law; convex order is proved for every convex function.
3. Convexity of `A -> trace(A^(2q))` on real symmetric matrices is proved by
   exact noncommutative derivatives and spectral diagonalization.
4. The iid trace moment is identified with an exact finite Fock vacuum moment;
   the degenerate `b=1` case is separately realized on a literal two-level
   product space and identified with its explicit lifted-J operator.
5. All normalized bands are decomposed into light, mixed, directional, and
   heavy pieces, and every piece has a proved restricted operator norm.
6. Ladder iteration gives the trace moment; matrix Markov gives the operator
   tail; exact Gram/OSE equivalence gives the vector statement.
7. Certified exponential, square-root, ceiling, and base-two logarithm bounds
   discharge all constants and strict integer sizes.

## Trust and reproducibility

The project is pinned to Lean/mathlib v4.33.0. The completion gate is:

```text
lake build
lake env lean SparseFockFormal/AxiomAudit.lean
lake env lean SparseFockFormal/EndgameAxiomAudit.lean
```

`AxiomAudit.lean` and `EndgameAxiomAudit.lean` print the axioms of the final
theorems and the main analytic/combinatorial seams. The final matrix theorem
depends only on standard Lean/mathlib foundations: `propext`,
`Classical.choice`, and `Quot.sound`. A source sweep rejects `sorry`,
`admit`, project-defined `axiom`, `unsafe`, `partial`, `opaque`,
`implemented_by`, and `native_decide` proof escapes.
