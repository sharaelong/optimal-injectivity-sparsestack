# Machine-verified sparse-Fock proof and distributional extensions for the Nelson-Nguyen upper edge

> **Status: complete Lean verification of the fixed-matrix theorem and the scoped extensions below; not peer reviewed; no priority claim.**
>
> This repository records a machine-verified proof for the upper spectral edge of the
> **fully independent SparseStack** oblivious subspace embedding at the
> Nelson-Nguyen parameter scale. The formal theorem has no uninstantiated
> analytic or probabilistic hypotheses. Conventional review remains relevant
> to statement correspondence, exposition, attribution, and novelty.

The companion extension machine-verifies exact moment transfer for SparseStack
laws whose combined signed-selector marginals match through order $4q$, a
dyadic finite-field seed-cardinality certificate, and the canonical independent
uniform signed exact-$s$ OSNAP theorem. It also verifies the exact-$s$
moment and tail bounds under whole-column matching through order $4q$. These
results reuse, rather than restate, the fully independent sparse-Fock analysis.

The claimed parameter regime is

$$
m = O\left(\frac{d+\log(1/\delta)}{\varepsilon^2}\right),
\qquad
s = O\left(\frac{1+\log(d/\delta)}{\varepsilon}\right),
$$

where `m` is the number of rows and `s` is the number of nonzeros per column.
The extension is distribution-specific: it does **not** prove the theorem for
every abstract negatively correlated OSNAP law. Its dyadic generator is an
exact finite-law and seed-cardinality certificate, not a verified bit-level
hashing implementation. The separate-sign/$2q$-hash refinement and optional
`408608` dyadic row constant are paper-only; no short-seed sampler is claimed
for the exact-column alphabet.

## Start here

- [Canonical technical report (PDF)](paper/nelson_nguyen_sparse_fock_candidate_proof.pdf)
- [Clarified version](paper/V1.6.pdf)
- [Canonical technical report (LaTeX)](paper/nelson_nguyen_sparse_fock_candidate_proof.tex)
- [Formalization scope](formal/README.md)
- [Extension report: limited independence and uniform exact-s OSNAP (PDF)](extensions/limited-independence-exact-s-osnap/report/limited_independence_uniform_exact_s_osnap.pdf)
- [Extension report (LaTeX)](extensions/limited-independence-exact-s-osnap/report/limited_independence_uniform_exact_s_osnap.tex)
- [Extension formalization ledger](extensions/limited-independence-exact-s-osnap/lean/FORMALIZATION.md)
- [Verification guide](verification/README.md)
- [External references](REFERENCES.md)
- [Provenance and inclusion manifest](PROVENANCE.md)

The canonical report is version 1.5, dated 16 August 2026. The extension report
is version 1.0, dated 17 August 2026.

## Repository layout

- `paper/`: the canonical end-to-end proof document and its compiled PDF.
- `formal/`: one Lean 4 + mathlib project, with toolchain and dependency manifest.
- `extensions/`: companion results. The limited-independence/exact-`s` package
  contains its report and a self-contained Lean project snapshot with the
  original proof modules and all extension modules.
- `verification/`: finite-dimensional falsification and regression programs.
  These programs support the audit trail; numerical evidence is not substituted
  for any load-bearing proof step.
- `reviews/`: cross-model referee reports and the formalization audit.
- `history/`: superseded working notes, including explicit retractions. These are
  preserved for research transparency and must not be cited as current proofs.
- `transcripts/`: a curated collaboration transcript plus its redaction notice.

## Machine-verified formalization

The Lean 4 project formalizes the complete fixed-matrix theorem for the fully
independent signed-hash SparseStack law. Its final endpoint is
`SparseFock.MainTheorem.fully_independent_sparseStack_matrix`; it has no
uninstantiated band, moment, coupling, convexity, or probability hypotheses.
The final axiom audit reports only the standard Lean/mathlib foundations
`propext`, `Classical.choice`, and `Quot.sound`. The source contains no `sorry`,
`admit`, project-defined `axiom`, `unsafe`, `partial`, `opaque`,
`implemented_by`, or `native_decide` proof escapes. See
[formal/README.md](formal/README.md) for the source-coverage ledger and audit
commands.

The extension project adds machine-checked endpoints for the precise laws
studied in the companion report:

- `SparseFock.SparseStackLimitedIndependence.rounded_operator_norm_failure_le_delta`
  for combined-selector marginal matching through order $4q$;
- `SparseFock.UniformExactS.uniformExactS_main` for independent uniform signed
  exact-$s$ columns, with the same explicit `1356` and `306456` bounds; and
- `SparseFock.UniformExactS.rounded_operator_norm_failure_le_delta_of_matchesUpTo`
  for whole-column marginal matching through order $4q$.

The finite-field modules additionally certify a balanced polynomial generator,
exact seed cardinality, and a dyadic generated-law tail under their explicit
field-size and capacity premises. The extension axiom audits again report only
`propext`, `Classical.choice`, and `Quot.sound`. See the
[extension ledger](extensions/limited-independence-exact-s-osnap/lean/FORMALIZATION.md)
for exact statements and scope boundaries.

## Building the papers

A TeX Live or MiKTeX installation with `latexmk` is sufficient:

```powershell
cd paper
latexmk -pdf nelson_nguyen_sparse_fock_candidate_proof.tex

cd ../extensions/limited-independence-exact-s-osnap/report
latexmk -pdf limited_independence_uniform_exact_s_osnap.tex
```

Generated LaTeX intermediates are ignored; the reviewed PDF is committed.

## Attribution and disclosure

Research direction and authorship: **Diar Heidary**
([diyar.heydari83@sharif.edu](mailto:diyar.heydari83@sharif.edu)).

The mathematical development was produced in a human-directed collaboration with
**ChatGPT 5.6 Sol** (OpenAI) and **Claude Fable 5** (Anthropic). The two systems
alternated between proposing arguments and attempting to refute them. Multiple
intermediate claims failed and are preserved with retraction notices in `history/`.
Cross-model checking is not a substitute for independent human refereeing.

## Citation and license

Citation metadata is provided in [CITATION.cff](CITATION.cff). Unless a file says
otherwise, this repository is released under the [MIT License](LICENSE).
