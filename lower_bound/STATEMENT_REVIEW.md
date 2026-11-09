# Statement Review: `Osi/Spec.lean` vs. *"Optimal Injectivity of the SparseStack"*

- **Source Manuscript:** `source/constant_injectivity_sparsestack.pdf` (50 pages, SHA-256 `045f0795c68732002391ebbe773dfa4bcf7e43866484f00a5af1f8ed5a1e9588`)
- **Formal Specification:** `Osi/Spec.lean` (imports `Mathlib` only; `0 sorry`, `0 axiom`, `scan_forbidden.py` clean with `0` violations)

---

## 1. Core Modeling Conventions

1. **Matrices, Norms, Isometries, and Singular Values (`Osi/Spec.lean` §1):**
   - Matrices in $\mathbb{R}^{n \times k}$ are `Matrix (Fin n) (Fin k) ℝ`.
   - `vecSqNorm v = ∑ i, (v i)^2` ($\|v\|_2^2$), `frobSq A = ∑ i, ∑ j, (A i j)^2` ($\|A\|_F^2$), `spectralNorm A = ‖Matrix.toEuclideanLin A‖` ($\|A\|_{2 \to 2}$).
   - `LoewnerLe A B = (B - A).PosSemidef` ($A \preceq B$, i.e. $B - A$ is symmetric and $x^\top (B - A) x \ge 0$ for all $x$).
   - `IsIsometry Q = (Q.transpose * Q = 1)` ($Q^\top Q = I_r$, orthonormal columns).
   - `MinEigenvalueAtLeast A α` states that every eigenvalue of the symmetric Gram matrix $A^\top A$ (`Aᴴ * A` over `ℝ`) is at least $\alpha$, i.e. $\sigma_{\min}(A)^2 = \lambda_{\min}(A^\top A) \ge \alpha$. `QuadraticLowerBound A α` is the Rayleigh-quotient form $\forall x \in \mathbb{R}^r,\; \|A x\|_2^2 \ge \alpha \|x\|_2^2$.
   - `distSparseSq m z = ⨅_{|I| \le m} ∑_{i \notin I} z_i^2` ($d_m(z)^2$, distance to $m$-sparse vectors, Section 2 p. 7 & Section 3 p. 15).
   - `coordFrame R hR : Matrix (Fin n) (Fin r) ℝ` ($Q_R = I_R$ for $R \in \binom{[n]}{r}$) has columns $e_i$ ($i \in R$) in increasing order, so $S^\top Q_R$ is the exact $k \times r$ transposed coordinate submatrix $S_R^\top$.

2. **Row Sparsity, Overlap Condition (Definition 1.2), and Random Matrix Distributions (`Osi/Spec.lean` §2):**
   - `rowSupport S i = {j ∈ Fin k | S i j ≠ 0}` ($\operatorname{supp}(s_i)$).
   - `overlapPairCount S` counts unordered pairs $\{u, v\} \subset [n]$ ($u < v$) with $|\operatorname{supp}(s_u) \cap \operatorname{supp}(s_v)| \ge 2$.
   - **Definition 1.2 (`SatisfiesOverlapCond S η`, p. 3 line 258):**
     `(overlapPairCount S : ℝ) ≤ η * ((n : ℝ)^2 / (k : ℝ))`, matching $\sum_{1 \le u < v \le n} \mathbf{1}\{|\operatorname{supp}(s_u) \cap \operatorname{supp}(s_v)| \ge 2\} \le \eta \frac{n^2}{k}$ verbatim.
   - **Kolmogorov Random Matrix Representation:** Because `Matrix m n ℝ` does not carry a global `MeasurableSpace` instance in Mathlib (and `instance` declarations are forbidden in `Spec.lean`), random matrices are quantified universally over **all** probability spaces `(Ω_prob : Type) [MeasurableSpace Ω_prob] (P : MeasureTheory.Measure Ω_prob) [IsProbabilityMeasure P]` and entrywise Borel-measurable maps `M : Ω_prob → Matrix (Fin n) (Fin k) ℝ` (`IsRandomMatrix M := ∀ i j, Measurable (fun ω => M ω i j)`).
     - Any Borel probability law $\mu$ on $\mathbb{R}^{n \times k}$ (`Fin n → Fin k → ℝ`, which has Mathlib's product Borel `MeasurableSpace`) is immediately an instance via `(Ω_prob := Fin n → Fin k → ℝ, P := μ, M := Matrix.of)`.
     - Finite discrete ensembles such as `SparseStack` (`Ω_prob := SketchSample ζ b n`, `P := sparseStackMeasure ζ b n`, `M := sparseStackOmega`) also instantiate the exact same predicates directly.
   - **Shared Predicates Across Upper and Lower Bounds:**
     - `IsIsotropic P M`: entrywise integrability and $\mathbb{E}_P[M M^\top] = I_n$.
     - `IsRowSparse P M ζ`: $\forall^{\mathrm{ae}} \omega,\; \forall i,\; |\operatorname{supp}((M \omega)_i)| \le \zeta$.
     - `SatisfiesOverlapWhp P M η p_ov`: $P(\text{SatisfiesOverlapCond}(M \omega, \eta)) \ge p_{\mathrm{ov}}$.
     - `IsOSIWithProb P M r α p_osi`: $\forall Q \in \mathbb{R}^{n \times r}$ with $Q^\top Q = I_r$, $P(\sigma_{\min}((M \omega)^\top Q)^2 \ge \alpha) \ge p_{\mathrm{osi}}$.
     - `IsOSI P M r α := IsOSIWithProb P M r α (19 / 20)` (matching `19/20` in both Theorem 1.1 p. 3/34 and Lemma 10.1 proof p. 46 line 4306; we also state `Theorem_1_3_LowerBound_HalfProb` at $p_{\mathrm{osi}} = 1/2$, which simultaneously covers $1/2$, $9/10$, and $19/20$).

---

## 2. Side-by-Side Mapping of All 35 `Prop` Statements

### Section 1.1 — Main Results & Shared-Vocabulary Tightness

| Lean `Prop` in `Osi/Spec.lean` | Paper Reference | Plain Mathematical Statement & Modeling Notes |
|---|---|---|
| `Theorem_1_1_GeneralParams` | Theorem 1.1 (pp. 1, 3, 34) | For $C = 32768$, $K = 160{,}000{,}000$, $\alpha = \frac{12{,}256{,}937}{119{,}880{,}000{,}000} \in (10^{-4}, 1)$, for all $n \ge r \ge 2$ and all integers $\zeta, b$ with $\zeta \ge C\sqrt{\log(e r)}$, $b \ge 2$, and $k = \zeta b \ge K r$, $\Omega_{\zeta,b} \sim \operatorname{SparseStack}(\zeta, b, n)$ satisfies `IsProbabilityMeasure`, `IsRandomMatrix`, `IsIsotropic`, `IsRowSparse _ _ ζ`, and `IsOSI` ($\ge 19/20$, both under `sparseStackMeasure` and `uniformProb`). |
| `Theorem_1_1_PaperRange` | Theorem 1.1 (pp. 1, 3) | Existential window form (paired with the universal form `Theorem_1_1_GeneralParams` above): $\exists C, K > 0, \alpha \in (0,1)$ such that for every $n \ge r \ge 2$ and $C_{\mathrm{up}} \ge 2C$, there exist $\zeta \ge 1, b \ge 2$ inside the window $C\sqrt{\log(e r)} \le \zeta \le C_{\mathrm{up}}\sqrt{\log(e r)}$ and $K r \le \zeta b \le 2 K r$ giving an isotropic row-$\zeta$-sparse $(r, \alpha)$-OSI. |
| `Theorem_1_1_Schedule` | Theorem 1.1 (pp. 34–36) | Canonical schedule $\zeta = \lceil C\sqrt{\log(e r)} \rceil$, $b = \lceil K r / \zeta \rceil$: $\alpha \in (10^{-4}, 1)$, $b\zeta \le K r + \zeta \le (K + C + 1) r$, $\mathbb{E}[\Omega\Omega^\top] = I_n$, and $\Pr[\sigma_{\min}(\Omega^\top Q)^2 \ge \alpha] \ge 19/20$. |
| `Proposition_SparseStack_Overlap` | Section 1.1 after Def. 1.2 (pp. 3–4) | For all $n \ge 0$ and $\zeta, b \ge 1$ ($k = \zeta b$), $\Omega_{\zeta,b}$ satisfies Definition 1.2 with $\eta = \frac{5\zeta^4}{2k} = O(\zeta^4/k)$ with probability $\ge 9/10$. |
| `Theorem_1_3_LowerBound_HalfProb` | Theorem 1.3 (p. 4) / Thm 10.2 (p. 46) | Stronger $1/2$-probability lower bound: for any $K \ge 1, \alpha \in (0,1)$, $\exists c, C_H, C_n > 0, r_0 \ge 3$ such that for $r \ge r_0$, $n \ge \max\{r, C_n r (\log r / \log\log r)^3\}$, $k \le K r$, any isotropic row-$\zeta$-sparse random matrix satisfying Def. 1.2 at $\eta = (C_H \zeta^6)^{-1}$ w.p. $\ge 9/10$ and `IsOSIWithProb _ _ r α (1/2)` must satisfy $\zeta \ge c\sqrt{\log r / \log\log r}$. |
| `Theorem_1_3_LowerBound` | Theorem 1.3 (p. 4) | Same lower bound under the paper's `IsOSI` ($19/20$) predicate. |
| `Theorem_1_3_QuadraticN` | Theorem 1.3 + `[NN13]` discussion (p. 4) | Specialization of `Theorem_1_3_LowerBound` to all $n \ge 100 r^2$ (matching Nelson–Nguyễn's quadratic ambient condition). |
| `Theorem_1_3_NecessityOfAmbientBound` | Necessity of ambient guard ($n > K r$) in Thm 1.3 | Formal proof that whenever $2 \le r \le n \le K r$, the deterministic identity matrix $\Omega = I_n \in \mathbb{R}^{n \times n}$ ($k = n \le K r$) satisfies isotropy, $\zeta = 1$, $\eta = 0$ w.p. $1$, and $\sigma_{\min}(\Omega^\top Q)^2 = 1 \ge \alpha$ w.p. $1$, proving that excluding the $n \le K r$ identity regime is mathematically necessary (without claiming optimality of the polylogarithmic exponent $3$ in $C_n r (\log r / \log\log r)^3$). |
| `Theorem_Optimal_SparseStack_Tightness` | Section 1.1 Tightness Synthesis | Proves in one unified statement (with identical `C_H`, `K_tot`, `constAlpha`, and predicates) that `SparseStack` satisfies all hypotheses of `Theorem_1_3` at $\zeta \le 2C\sqrt{\log(e r)}$ for $n \ge 100 r^2$, while every distribution satisfying those same hypotheses must have $\zeta \ge c\sqrt{\log r / \log\log r}$. |

### Sections 2–6 — Upper-Bound Pipeline

| Lean `Prop` in `Osi/Spec.lean` | Paper Reference | Plain Mathematical Statement & Modeling Notes |
|---|---|---|
| `Theorem_2_1_FlatPreservation` | Theorem 2.1 (pp. 7, 19) | Full general $(\varepsilon, \delta_{\mathrm{loc}}) \in (0,1)^2$ flat-vector localization with universal linear scaling $\lambda \ge c_{\lambda}\varepsilon$ ($c_\lambda > 0$): $\exists \lambda \ge c_\lambda \varepsilon, \Theta, M_{\mathrm{loc}} \ge 1, r_0 \ge 1$ such that for $n \ge r \ge r_0$, $1 \le \zeta \le r$, $\zeta b \ge \Theta r$, $\zeta m \ge M_{\mathrm{loc}} r$, $\Pr[\exists x \in S^{r-1} : d_m(Qx) \ge \varepsilon,\; \|\Omega^\top Q x\| < \lambda] \le \delta_{\mathrm{loc}}$. |
| `Theorem_2_2_CommonSupport` | Theorem 2.2 (pp. 8, 22) | Deterministic spiky common-support extraction for general $m \ge 1, \varepsilon > 0, \lambda > 0$: $\exists I \subseteq [n]$ with $|I| \le 8m$ and $Q_{I^c}^\top Q_{I^c} \preceq \frac{8}{3}\varepsilon^2 I_r + \frac{8}{3\lambda^2} X^\top X$. |
| `Theorem_2_3_HeavyPreservation` | Theorem 2.3 (pp. 9, 33) | Full general $t_0 \in (0, 1/4), \delta_{\mathrm{rep}} \in (0,1)$ heavy-coordinate preservation with $\beta \ge \frac{1}{3}(\frac{11}{12} - 2t_0) > 0$: w.p. $\ge 1 - \delta_{\mathrm{rep}}$, both $\|Y x\|^2 \ge \beta \|(Qx)_I\|^2 - t_0 \|(Qx)_{I^c}\|^2$ for all $x \in \mathbb{R}^r$ and $Y^\top Y + (\beta + t_0) Q_{I^c}^\top Q_{I^c} \succeq \beta I_r$. |
| `Lemma_3_2_WeightedBernoulli` | Lemma 3.2 (p. 16) | General $p_0 > 0$, independent $\{0,1\}$-valued $B_j$ on any probability space with $P(B_j = 1) \ge p_0$ and $0 \le v_j \le v_{\max}$: $P(\sum_j v_j B_j < c_1 V_0) \le \exp(-c_2 V_0 / v_{\max})$. |
| `Lemma_3_3_PointwiseFlat` | Lemma 3.3 (p. 17) | Pointwise small-ball bound for $w = h + a z$ with disjoint supports, $\|z\|_2 = 1$, $\|z\|_\infty^2 \le D^{-1}$, $1 \le D \le b$: $\Pr[\|\Omega^\top(h + az)\|_2 < c_0 a] \le 2 e^{-c_{\mathrm{sb}} \zeta D}$. |
| `Lemma_3_4_LatticeRounding` | Lemma 3.4 (p. 18) | Unbiased lattice net $N_\eta \subset (1+\eta) B_2^r$ of size $\le (16/\eta)^r$ with $\|x - y\|_2 \le \eta$ and $\|T(x - y)\|_2^2 \le \frac{\eta^2}{4r}\|T\|_F^2$. |
| `Lemma_4_1_GaussianTruncation` | Lemma 4.1 (p. 21) | Expected squared $m$-tail $E[d_m(g)^2] \ge \frac{3}{4} \sum_{i > 4m} a_{\sigma(i)}$ for any random vector $g$ ($n > 4m$) with marginal kurtosis $E[g_i^4] \le 3 (E[g_i^2])^2$ (equality for centered Gaussians) and non-increasing variance order $\sigma$. |
| `Lemma_4_2_MinimaxSelection` | Lemma 4.2 (p. 22) | General minimax common-coordinate extraction: $d_m(Vx)^2 \le x^\top H x$ ($H \succeq 0, m \ge 1$) $\implies \exists |I| \le 8m,\; V_{I^c}^\top V_{I^c} \preceq \frac{8}{3} H$. |
| `Lemma_5_3_IidOpNorm` | Lemma 5.3 (p. 25) | Independent-entry $\{\pm 1, 0\}$ matrix ($B \ge 2, a \ge 1, m = aB$) for all $p \ge \max\{1, \log(2d)\}$: $\mathbb{E}[\|X W\|^2] \le C_{\mathrm{ind}}(a + D_p/B + p)$. |
| `Lemma_5_4_IsolatedCrossTerm` | Lemma 5.4 (p. 27) | Conditional expectation of $\|\tilde{H}^\top \tilde{Y}\|$ given $\Omega_{\zeta,b,I}$ for $b \ge 2\zeta$ and all $p \ge \max\{1, \log(2d)\}$, plus exact vanishing when $I = \emptyset$ or $d = 0$. |
| `Lemma_5_5_FullSketchMoment` | Lemma 5.5 (p. 28) | $2p$-th operator-norm moment bound for $G - I_D = U^\top \Omega \Omega^\top U - I_D$ ($b \ge 2, \zeta \ge 1, D \ge 1, p \ge 1$). |
| `Lemma_6_1_SingleGroup` | Lemma 6.1 (p. 30) | Single-group norm preservation for arbitrary $t_0 > 0, \delta_{\mathrm{rep}} \in (0,1), H_0 > 0$, conditioned on any head realization $\omega_0$ of $I_0$. |
| `Lemma_6_2_TwoGroupIsolation` | Lemma 6.2 (p. 31) | Two-group balls-into-bins isolation ($b \ge 1, R \ge 2, |I| \le \min\{R, b/16\}$) for arbitrary $\delta_{\mathrm{rep}} \in (0,1)$ with the **exact printed constant $c_1 = 1/1152$** in both parts (i) and (ii). |
| `Lemma_6_3_TwoGroupHeavy` | Lemma 6.3 (p. 32) | Two-group heavy-coordinate lower bound for arbitrary $t_0 \in (0, 1/4), \delta_{\mathrm{rep}} \in (0,1)$ across both high-sparsity ($\zeta \ge H_{\mathrm{rep}}\log(eR)$) and moderate-sparsity ($\zeta < H_{\mathrm{rep}}\log(eR)$) regimes. |

### Sections 8–10 — Lower-Bound Pipeline

| Lean `Prop` in `Osi/Spec.lean` | Paper Reference | Plain Mathematical Statement & Modeling Notes |
|---|---|---|
| `Lemma_8_1_HeavyRowCount` | Lemma 8.1 (p. 37) | $\|S\|_F^2 \le 10 n \implies |I_{\mathrm{heavy}}| \le n / 16$ ($M = 160$). |
| `Lemma_8_2_SmallOrOneSparseElim` | Lemma 8.2 (p. 37) | If $|I_{\mathrm{small}}| \ge n/16$ or $|I_{\mathrm{one}}| \ge n/16$ with $k \le K r$, $r \ge C_0 K$, and $n \ge 64 K r$, then $\Pr_{R \sim \operatorname{Unif}\binom{[n]}{r}}(\sigma_{\min}(S_R^\top)^2 < \alpha) \ge 9/10$. |
| `Lemma_8_3_C4FreeSubgraph` | Lemma 8.3 (p. 38) | Subsampling $V_0 \in \binom{[n]}{n_0}$ ($n_0 = \lceil C_{\mathrm{samp}} r \zeta^6 / \alpha \rceil \le n$) under $\eta \le (512 C_{\mathrm{samp}} \zeta^6 / \alpha)^{-1}$ and $|V_{\mathrm{clean}}| \ge 13n/16$ yields $N_{\mathrm{bad}} \le n_0/4$, $N_{\mathrm{coll}} \le n_0/16$, $|V(G_0)| \ge 5n_0/8$ ($V(G_0) \subseteq V_0$, so $|V(G_0)| \le n_0$), $C_4$-freeness, and $\alpha \le \|s_i\|_2^2 \le 160$, $2 \le |\operatorname{supp}(s_i)| \le \zeta$ w.p. $\ge 7/8$. |
| `Lemma_9_1_TreeCancellation` | Lemma 9.1 (p. 40) | In $C_4$-free $V_{G_0}$, `treeCancelVec` satisfies $(S^\top x)_j = 0$ on $j \in \operatorname{supp}(s_{i^*})$ and $\sum_{c \notin \operatorname{supp}(s_{i^*})} |(S^\top x)_c|^2 \le d \|s_{i^*}\|_2^2 / q$. |
| `Lemma_9_2_SingleTreeDisjointLeaves` | Lemma 9.2 (p. 41) | Greedy extraction of $q$-leaf subsets $L_j \subseteq F_j$ with pairwise disjoint outer supports $\operatorname{supp}(s_\ell) \setminus \{j\}$ from $|F_j| \ge q + q(\zeta - 1)^2$ in $C_4$-free $V_{G_0}$. |
| `Lemma_9_3_TuranCaroWei` | Lemma 9.3 (p. 42) | Every finite simple graph $H$ on $m \ge 1$ vertices has an independent set of size $\ge m / (1 + 2|E_H|/m)$. |
| `Lemma_9_4_TuranCenterRows` | Lemma 9.4 (p. 42) | For $(5/8) n_0 \le |V_{G_0}| \le n_0$: virtual-column splitting ($k' \le 2k$, cap $\Delta = \lceil \zeta n_0 / k \rceil$, top-$D$ relative-weight sets $F_{j'}$) and Turán extraction of $I_{\mathrm{center}} \subseteq V_{G_0} \setminus \bigcup_{j'} F_{j'}$ of size $\ge c_T r / \zeta^5$ with pairwise disjoint virtual-column supports. |
| `Lemma_9_5_HallMarriage` | Lemma 9.5 (p. 43) | Exact iff characterization of saturating matchings in finite bipartite graphs via $|N(A)| \ge |A|$. |
| `Lemma_9_6_DisjointLeafReservoirs` | Lemma 9.6 (p. 43) | Simultaneous allocation of pairwise disjoint $L$-subsets $R_{j'} \subseteq F_{j'}$ ($j' \in J_{\mathrm{branch}}$) when $|F_{j'}| \ge D \ge \zeta L$ and each row belongs to $\le \zeta$ active candidate sets. |
| `Theorem_9_7_WitnessForest` | Theorem 9.7 (p. 44) | For $(5/8) n_0 \le |V_{G_0}| \le n_0$: existence of $T \ge c_T r / \zeta^5$ ($T \ge 1$) pairwise row-disjoint padded witness row-sets $V(T_s) \subseteq V_{G_0}$ of **exact** size $1 + \zeta q$ ($q = \lceil 640 \zeta / \alpha \rceil$) and vectors $x^{(s)}$ supported inside $V(T_s)$ (`∀ i, i ∉ V_tree s → x_tree s i = 0`) with $\|x^{(s)}\|_2^2 \ge 1$ and $\|S^\top x^{(s)}\|_2^2 \le \alpha / 4$. (A star center of active degree $d_s \le \zeta$ uses $1 + d_s q$ active rows and is padded with $(\zeta - d_s) q$ unused rows of $V_{G_0}$ on which $x^{(s)} = 0$, giving uniform set size $1 + \zeta q$ for hypergeometric capture.) |
| `Lemma_10_1_CoordinateSubspaceReduction` | Lemma 10.1 (p. 45) | Coordinate-subspace minimax/Fubini reduction refuting `IsOSIWithProb P M r α p_osi` for every $p_{\mathrm{osi}} > 9/20$. |
| `Theorem_10_2_FiniteScale` | Theorem 10.2 (p. 46) | Fixed-matrix uniform coordinate capture bound $\Pr_R(\sigma_{\min}(S_R^\top)^2 \ge \alpha) \le 1/4$ under $\zeta \le c\sqrt{\log r / \log\log r}$ + deduction of the full lower bound. |

---

## 3. Manuscript Subtleties Uncovered & Addressed Explicitly

1. **Necessity of an Ambient-Dimension Lower Bound ($n > K r$) in Theorem 1.3 & Theorem 10.2:**
   - Theorem 1.3 (p. 4) and Theorem 10.2 (p. 46) write *"Let $n \ge r \ge 2$, $k \le K r$"* without printing an explicit lower bound on $n$ relative to $K r$ and $r \operatorname{polylog}(r)$.
   - However, when $2 \le r \le n \le \lfloor K r \rfloor$, setting $k = n \le K r$ and $\Omega = I_n$ deterministically satisfies $\mathbb{E}[\Omega\Omega^\top] = I_n$, row sparsity $\zeta = 1$, overlap $\eta = 0$, and $\sigma_{\min}(\Omega^\top Q)^2 = \sigma_{\min}(Q)^2 = 1 \ge \alpha$ w.p. $1$ for every isometry $Q$, contradicting $\zeta = \Omega(\sqrt{\log r / \log\log r})$.
   - Internally, Lemma 8.2 (p. 37 line 3579) uses $m_j - 1 \ge n / (64 K r)$ (requiring $n \ge 64 K r$) and $r \ge C_0 K$, while Lemma 8.3 (p. 38 line 3657) subsamples $n_0 = \lceil C_{\mathrm{samp}} r \zeta^6 / \alpha \rceil$ rows without replacement from $[n]$ (requiring $n_0 \le n$). Under the contradiction hypothesis $\zeta \le c\sqrt{\log r / \log\log r}$ of Theorem 10.2, $n_0 \le n$ holds whenever $n \ge C_n(K, \alpha)\, r (\log r / \log\log r)^3$ — and in particular for all $n \ge 100 r^2$ (matching Nelson–Nguyễn `[NN13]`, cited right below Theorem 1.3 on p. 4 line 290).
   - `Osi/Spec.lean` formalizes **both** the polylogarithmic-guard lower bound (`Theorem_1_3_LowerBound`), the quadratic-$n$ corollary (`Theorem_1_3_QuadraticN`), **and** the formal $\Omega = I_n$ counterexample (`Theorem_1_3_NecessityOfAmbientBound`) proving necessity of excluding the $n \le K r$ identity regime.
2. **Lemma 6.2 Exact Constant $c_1 = 1/1152$:**
   - In Lemma 6.2's proof (p. 31 line 3014), McDiarmid's inequality gives $\exp(-2(1/48)^2 \zeta_0) = \exp(-\zeta_0/1152)$, which the proof writes as $e^{-2 c_1 \zeta_0}$ with $c_1 = 1/1152$ (dropping a factor of $2$ in the McDiarmid exponent).
   - Nevertheless, because the $\zeta_0$ blocks are mutually independent and each per-block collision probability is at most $1/16$, a direct binomial MGF bound with base $5/4$ gives $((65/64)(4/5)^{1/12})^{\zeta_0} < e^{-\zeta_0 / 576} = e^{-2 c_1 \zeta_0}$! Thus `Lemma_6_2_TwoGroupIsolation` preserves the **exact printed constant $c_1 = 1/1152$** verbatim.
3. **Lemma 9.1 `C_4`-Freeness of $G_0$, Lemma 9.4 Subsample Size $|V(G_0)| \le n_0$, & Theorem 9.7 Padded Witness Sets:**
   - Lemma 9.1's proof (line 3818) uses that no leaf $\ell \in L_{j_1}$ of branch $j_1$ contains another branch column $j_2 \ne j_1$ of $i^*$. This follows from $i^*$ and all leaves lying in the $C_4$-free subgraph $G_0$ (`IsC4FreeRows S V_G0`), matching *"let $s_{i^*}^\top$ be a row in $G_0$"* on line 3780.
   - Similarly, Lemma 9.4 (line 4014) uses $\sum_{j=1}^k \deg_{G_0}(j) \le \zeta |V(G_0)| \le \zeta n_0$ (since $V(G_0) \subseteq V_0$ with $|V_0| = n_0$) to bound $k' \le 2k$; `V_G0.card ≤ n₀` is included explicitly in `Lemma_9_4_TuranCenterRows` and `Theorem_9_7_WitnessForest`, and `1 ≤ b` is included in `Lemma_6_2_TwoGroupIsolation` so `SketchSample ζ₀ b n` is non-empty when $I = \emptyset$.
   - In Theorem 9.7, each star center $s$ has degree $d_s \le \zeta$ in $G_0$, giving $1 + d_s q$ active tree rows; because $T(1 + \zeta q) \le \frac{5}{8} n_0 \le |V_{G_0}|$, each witness set $V(T_s)$ is padded with $(\zeta - d_s) q$ unused rows of $V_{G_0}$ (with $x^{(s)}_i = 0$ on padded rows) so all $T$ pairwise-disjoint row sets have uniform cardinality $1 + \zeta q$.

---

## 4. What `Osi/Spec.lean` Does NOT Claim

- The algorithmic consequences in Section 1.1 (pp. 4–5: sketch-and-solve least-squares regression and column subset selection) are reductions cited from `[CEMT25]` rather than numbered theorems proved in the manuscript, and are not claimed in `Osi/Spec.lean`.
- Literature background facts (`Fact 3.1` McDiarmid `[McD89]`, `Fact 5.1` `[Hei26]`, `Fact 5.2` `[Tro15]`) are used internally via zero-axiom Lean proofs (`SparseStack/Prob/McDiarmid.lean`, `vendor/heidary_formal/`, and `SparseStack/MatrixConc/Chernoff.lean`) rather than assumed as axioms; no axioms outside `{propext, Classical.choice, Quot.sound}` appear anywhere.
