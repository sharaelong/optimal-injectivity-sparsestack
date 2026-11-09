# Optimal Injectivity of the SparseStack — Lean 4 Formalization

Machine-checked formal proof in **Lean 4 (`v4.33.1`)** accompanying the paper:
> **"Optimal Injectivity of the SparseStack"**

This repository formalizes both the **Upper Bound** (Theorem 1.1, Sections 1–7) and the **Lower Bound** (Theorem 1.3, Sections 8–10), confirming the optimal sparsity threshold $\Theta(\widetilde{\sqrt{\log r}})$ for linear-dimension Oblivious Subspace Injections (OSIs).

All theorems are formally verified with **0 `sorry`s**, **0 custom axioms** (relying only on Lean 4 standard axioms `propext`, `Quot.sound`, and `Classical.choice`), and **0 compiler warnings**.

---

## Repository Structure

The repository is organized into two standalone, independently verifiable packages:

```text
optimal-injectivity-sparsestack/
├── upper_bound/             # Upper Bound formalization (Sections 1–7, pp. 1–40)
│   ├── OsiUb/
│   │   ├── Spec.lean        # Formal specification of all 28 UB definitions & theorems
│   │   ├── Headline.lean    # Top-level exports of all 29 certified UB theorems
│   │   ├── Prelim/          # Singular value & Loewner order preliminaries
│   │   └── UpperBound/      # Detailed proofs (Sec 2–4, Sec 5, Sec 6, GeneralParams)
│   ├── SparseStack/         # Shared measure-theoretic, concentration & matrix libraries
│   ├── vendor/              # Vendored dependencies (Heidary [Hei26] moment bounds)
│   ├── lakefile.toml        # Lake package definition (target: OsiUb)
│   └── README.md            # Detailed documentation for the upper-bound formalization
│
├── lower_bound/             # Lower Bound formalization (Sections 8–10, pp. 40–55)
│   ├── Osi/
│   │   ├── Spec.lean        # Formal specification of lower-bound theorems & lemmas
│   │   ├── Headline.lean    # Top-level exports of certified LB theorems
│   │   ├── Prelim/          # Hypergeometric & singular value preliminaries
│   │   └── LowerBound/      # C4-free graph, tree cancellation, Turán & Hall matchings, endgame
│   ├── SparseStack/         # Shared supporting libraries
│   ├── vendor/              # Vendored dependencies
│   ├── lakefile.toml        # Lake package definition (target: Osi)
│   └── README.md            # Detailed documentation for the lower-bound formalization
│
└── README.md                # This file
```

---

## Key Results Formalized

### 1. Upper Bound (`upper_bound/`) — Theorem 1.1
- **SparseStack OSI Injectivity**: Row sparsity $\zeta = O(\sqrt{\log r})$ suffices for an isotropic SparseStack sketch matrix $\Omega_{\zeta,b} \in \mathbb{R}^{n \times k}$ at linear embedding dimension $k = \zeta b = \Theta(r)$ to satisfy:
  $$\mathbb{P}[\sigma_{\min}(\Omega_{\zeta,b}^\top Q)^2 \ge \alpha] \ge \frac{19}{20}$$
  for any fixed isometry $Q \in \mathbb{R}^{n \times r}$.
- **Core Pipeline**:
  - **Theorem 2.2**: Uniform preservation of flat vectors via randomized lattice rounding.
  - **Theorem 2.3**: Minimax common-support extraction for spiky vectors.
  - **Lemma 2.4**: Operator-norm bound on the cross-term via entrywise coupling and Jensen's inequality.
  - **Theorem 2.5**: Heavy-coordinate preservation in the independent second half via two-tier balls-into-bins isolation.

### 2. Lower Bound (`lower_bound/`) — Theorem 1.3
- **Fundamental Sparsity Barrier**: Any isotropic random sketching matrix $\Omega \in \mathbb{R}^{n \times k}$ ($k = O(r)$) satisfying the mild row-overlap condition (Definition 1.2) requires row sparsity:
  $$\zeta = \Omega\left(\sqrt{\frac{\log r}{\log \log r}}\right)$$
  to achieve linear-dimension injectivity.
- **Core Pipeline**:
  - **Section 8**: Deterministic row preprocessing and $C_4$-free bipartite subgraph $G_0$ extraction.
  - **Section 9**: Construction of a forest of $T = \Theta(r/\zeta^5)$ mutually vertex-disjoint witness cancellation trees via Turán's theorem and Hall's marriage theorem.
  - **Section 10**: Coordinate subspace reduction and witness tree capture probability analysis.

---

## Build & Verification

Prerequisite: [elan](https://github.com/leanprover/elan) (Lean version manager).

### Building the Upper Bound
```bash
cd upper_bound
lake exe cache get
lake build OsiUb
```

### Building the Lower Bound
```bash
cd lower_bound
lake exe cache get
lake build Osi
```
