# Provenance and inclusion manifest

This repository was assembled on 15 August 2026 from a larger private staging
archive, updated on 16 August 2026 with the audited complete Lean
formalization, and extended on 17 August 2026 with the limited-independence and
uniform exact-`s` companion package. The staging archives were left untouched.
The release is intentionally a curated research package rather than a
byte-for-byte dump of every local file.

## Included material

| Release area | Origin and treatment |
|---|---|
| `paper/nelson_nguyen_sparse_fock_candidate_proof.*` | Canonical report, revised to version 1.5 to record completion of the full fixed-matrix Lean theorem while retaining the fully-independent-only and non-peer-reviewed scope. |
| `formal/` | Audited complete Lean source project for the fixed-matrix theorem, copied without generated `.lake`, toolchain-installation, or build-cache directories. Its source-coverage ledger was adapted only to use repository-relative links and the report's version 1.5 line numbers. |
| `extensions/limited-independence-exact-s-osnap/report/` | Companion report v1.0 and reviewed PDF for combined-selector `4q` matching, the dyadic seed-cardinality certificate, and uniform signed exact-`s` OSNAP. LaTeX intermediates and rendered QA pages were omitted. |
| `extensions/limited-independence-exact-s-osnap/lean/` | Self-contained pinned Lean project snapshot containing every older core module and the new extension modules. Generated `.lake`, temporary, and replay-output directories were omitted. |
| `verification/` | The seven surviving Python verification and falsification programs. A stale prose label in `y_band_checks.py` was corrected to match the final bound; its implementation is unchanged. |
| `reviews/` | The initial assessment, report audit, and Lean audit addendum. Machine-specific staging paths were generalized. |
| `history/` | The v1-v6 sparse-Fock note sequence, including retraction notices. The byte-identical duplicate of v1 was omitted. Machine-specific script paths were replaced by relative release links. |
| `transcripts/ChatGPT_curated.md` | Derived from the pre-redacted ChatGPT export. Collapsed tool-call blocks, application inventory, session plumbing, local filesystem paths, and attachment locations were removed or generalized. |

## Material deliberately omitted

- the raw, unredacted ChatGPT export;
- the Claude session identifier (no Claude transcript export was present);
- downloaded papers, arXiv source archives, malformed extraction trees, and
  other third-party source material;
- duplicate working trees and the duplicate `sparse_fock_ladder_1.md`;
- local Lean installations, mathlib build caches, bootstrap executables, and
  archives (`.elan/`, `.lake/`, `.tooling/`);
- Python bytecode, LaTeX intermediates, rendered QA pages, temporary directories,
  numerical scratch data, and obsolete repository-generation scripts;
- exploratory programs for abandoned pre-sparse-Fock routes. Their conclusions
  are represented, where relevant, by the reviews and retraction history.

These exclusions reduce the release from a machine-specific working archive to a
self-contained package of source, reviewed PDFs, reproducibility material, and
the research audit trail. They do not remove any file required to build the Lean
project or run the retained verification programs.

## Key SHA-256 checksums

| File | SHA-256 | Bytes |
|---|---|---:|
| `paper/nelson_nguyen_sparse_fock_candidate_proof.tex` | `723e5390dfd7190030153476e6b5d2b4d1f1f8566cded80ecb0e6d1e8e975e96` | 56,056 |
| `paper/nelson_nguyen_sparse_fock_candidate_proof.pdf` | `3d5104739c539725c57734c1cea1979ab156e8f4599807de14a0495abaca9d73` | 494,313 |
| `formal/lean-toolchain` | `9031857cc2da4166d300c68c9881623ba06965003c551c868ab0754b10d07efd` | 27 |
| `formal/lake-manifest.json` | `01557d05559543dc01ab3448dc7a2d174f3648b64d793a8562f7625de74940aa` | 3,140 |
| `formal/SparseFockFormal.lean` | `56d1d4b9e62d72565ddb1ca0543bd1e1c3c2adaff2dbc4e2ed6c8929d1da6e00` | 2,059 |
| `extensions/limited-independence-exact-s-osnap/report/limited_independence_uniform_exact_s_osnap.tex` | `7afaa148907a385ba54d5b6ef400c0f18285a92f984fb6d18c1adc5fab6fab0e` | 32,234 |
| `extensions/limited-independence-exact-s-osnap/report/limited_independence_uniform_exact_s_osnap.pdf` | `3658b8a9bb7ac8ef194ed2c0c840d6cc2be0ac3ea6a7bfc143ba1da001002e57` | 412,987 |
| `extensions/limited-independence-exact-s-osnap/lean/SparseFockFormal.lean` | `9122cbe3cb9f46afe4ceac4c3bda8534b67af4aebaea773bd0136c82b0637c5e` | 2,638 |
| `transcripts/ChatGPT_curated.md` | `5df8551086e83bc0ba54f9f7e7dc6c1ebcf6d6daab7f1c979c65833c5b9275ae` | 72,044 |

`MANIFEST.sha256` records the checksum of every tracked release file except the
manifest itself. Recreate it after any intentional edit.

## Verification performed during curation

- The canonical report's PDF was rebuilt from its version 1.5 LaTeX source;
  its status page and Lean appendix were rendered and visually inspected, and
  the final log was checked for unresolved references and layout warnings.
- The copied Lean source set is the audited complete project. Generated build
  caches were excluded; the pinned build and the two dedicated axiom-audit
  commands are reproduced by the GitHub workflow.
- The extension report was rebuilt from its LaTeX source, and the copied
  extension Lean project passed a clean pinned build, direct replay of the
  theorem-bearing modules, the proof-escape sweep, and both axiom audits. The
  GitHub workflow reproduces the extension build, audits, and report build.
- The curated transcript was scanned for drive-qualified paths, home-directory
  paths, session IDs, tool-log markers, and common credential formats.
- A final whole-tree secret and artifact scan is run before publication. Such a
  scan reduces accidental disclosure risk but is not a cryptographic guarantee.
