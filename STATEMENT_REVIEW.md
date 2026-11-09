# Statement Review: `OsiUb/Spec.lean` vs. Upper Bound (Sections 1–7) of *"Optimal Injectivity of the SparseStack"* (Revised Manuscript)

- **Source Manuscript:** `source/constant_injectivity_sparsestack-2.pdf` (`621,220` bytes, 55 pages, SHA-256 `0fcf41b556c345609b17144961b536898f3248b5cc13f150d923b442672bef78`; Upper Bound covers Sections 1–7, pp. 1–40)
- **Formal Specification:** `OsiUb/Spec.lean` (`1,104` lines, `63,797` bytes, SHA-256 `fac86a78b27ec315857b605fc4553f85823b9aab9a622cca5100205f101985c7`, imports `Mathlib` only; `0 sorry`, `0 axiom`, `0` warnings, `scan_forbidden.py` clean with `0` violations)
- **Headline Proofs:** `OsiUb/Headline.lean` (`28` individual `Prop` statements + `AllUpperBoundTheorems` = **29 certified theorems**)

---

## 1. Core Modeling Conventions (`OsiUb/Spec.lean` §§1–5)

1. **Matrices, Norms, Isometries, Loewner Order, and Singular Values:**
   - Matrices in $\mathbb{R}^{n \times k}$ are `Matrix (Fin n) (Fin k) ℝ`; submatrix blocks indexed by finite coordinate sets $I, J \subseteq [n]$ are `Matrix I J ℝ` (`I, J : Finset (Fin n)`).
   - `vecSqNorm v = ∑ i, (v i)^2` ($\|v\|_2^2$), `frobSq A = ∑ i, ∑ j, (A i j)^2` ($\|A\|_F^2$), `spectralNorm A = ‖Matrix.toEuclideanLin A‖` ($\|A\|_{2 \to 2}$).
   - `LoewnerLe A B = (B - A).PosSemidef` ($A \preceq B$, i.e. $B - A$ is symmetric and $x^\top (B - A) x \ge 0$ for all $x$).
   - `IsIsometry Q = (Q.transpose * Q = 1)` ($Q^\top Q = I_r$, orthonormal columns).
   - `MinEigenvalueAtLeast A α`: every eigenvalue of the symmetric Gram matrix $A^\top A$ (`Aᴴ * A` over `ℝ`) is at least $\alpha$, i.e. $\sigma_{\min}(A)^2 = \lambda_{\min}(A^\top A) \ge \alpha$. `QuadraticLowerBound A α` is the Rayleigh-quotient form $\forall x \in \mathbb{R}^r,\; \|A x\|_2^2 \ge \alpha \|x\|_2^2$.
   - **Definition 2.1 (Flat vs. Spiky Vectors, p. 10):** `distSparseSq m z = ⨅_{|I| \le m} ∑_{i \notin I} z_i^2`, `distSparse m z = √(distSparseSq m z)` ($d_m(z) = \min_{|I| \le m} \|z_{I^c}\|_2$), `IsFlatVec m ε z = (ε ≤ distSparse m z)`, and `IsSpikyVec m ε z = (distSparse m z < ε)`.

2. **SparseStack Ensemble, Overlap Condition (Definition 1.2), and Measure Semantics:**
   - `SketchSample ζ b n = (Fin ζ → Fin n → Fin b) × (Fin ζ → Fin n → Bool)`: uniform probability (`uniformProb` and `sparseStackMeasure`) on this finite product space induces mutually independent uniform bucket hashes $s_{i,t} \sim \operatorname{Unif}([b])$ and uniform Rademacher signs $\sigma_{i,t} \sim \operatorname{Unif}(\{\pm 1\})$ across all $(t, i) \in [\zeta] \times [n]$.
   - `sparseStackOmega ω : Matrix (Fin n) (Fin (ζ * b)) ℝ` matches Section 1.2 (p. 5): row $i \in [n]$ places $\zeta^{-1/2} \sigma_{i,t}$ in output bucket $(t, s_{i,t})$ (`finProdFinEquiv (t, u)`) for each block $t \in [\zeta]$, so $\Omega_{\zeta,b}^\top \in \mathbb{R}^{k \times n}$ ($k = \zeta b$) stacks the $\zeta$ scaled CountSketch blocks vertically.
   - **Definition 1.2 (`SatisfiesOverlapCond S η`, p. 5):** `(overlapPairCount S : ℝ) ≤ η * ((n : ℝ)^2 / (k : ℝ))`, matching $\sum_{1 \le u < v \le n} \mathbf{1}\{|\operatorname{supp}(s_u) \cap \operatorname{supp}(s_v)| \ge 2\} \le \eta \frac{n^2}{k}$ verbatim.
   - Measure-theoretic OSI predicates (`IsRandomMatrix`, `IsIsotropic`, `IsRowSparse`, `SatisfiesOverlapWhp`, `IsOSIWithProb`, `IsOSI` at $19/20$) are stated over `MeasureTheory.Measure` and paired with explicit finite-product `uniformProb` / `uniformMeanMatrix` statements.

---

## 2. Side-by-Side Mapping of All 28 Upper-Bound `Prop` Statements (Sections 1–7)

| # | `OsiUb.Spec` Declaration | Paper Reference (`constant_injectivity_sparsestack-2.pdf`) | Mathematical Content & Fidelity Notes |
|---:|---|---|---|
| 1 | `Theorem_1_1_GeneralParams` | Theorem 1.1 (pp. 5, 39–40) | Universal $(\zeta, b)$ form at explicit $C = 32768$, $K = 160{,}000{,}000$, $\alpha = \frac{12{,}256{,}937}{119{,}880{,}000{,}000} \in (10^{-4}, 1)$: for all $n \ge r \ge 2$, $b \ge 2$, $\zeta \ge C\sqrt{\log(e r)}$, $\zeta b \ge K r$, $\Omega_{\zeta,b}$ satisfies `IsProbabilityMeasure`, `IsRandomMatrix`, `IsIsotropic`, `IsRowSparse _ _ ζ`, `IsOSI` ($\ge 19/20$), and `uniformProb ≥ 19/20`. |
| 2 | `Theorem_1_1_PaperRange` | Theorem 1.1 (p. 5) | Existential $\Theta(\sqrt{\log r})$ / $\Theta(r)$ window form: $\exists C, K > 0, \alpha \in (0,1)$ such that for all $n \ge r \ge 2$ and $C_{\mathrm{up}} \ge 2C$, some $\zeta, b \ge 2$ with $C\sqrt{\log(er)} \le \zeta \le C_{\mathrm{up}}\sqrt{\log(er)}$ and $Kr \le \zeta b \le 2Kr$ achieves isotropic row-$\zeta$-sparse $(r,\alpha)$-OSI. |
| 3 | `Theorem_1_1_Schedule` | Theorem 1.1 / Section 7 (pp. 5, 39–40) | Canonical schedule $\zeta = \lceil C\sqrt{\log(er)} \rceil$, $b = \lceil K r / \zeta \rceil$: $\alpha \in (10^{-4}, 1)$, $\zeta b \le K r + \zeta \le (K + C + 1) r$, $\mathbb{E}[\Omega\Omega^\top] = I_n$, and $\Pr[\sigma_{\min}(\Omega^\top Q)^2 \ge \alpha] \ge 19/20$. |
| 4 | `Proposition_SparseStack_Overlap` | Proposition after Def. 1.2 (pp. 5–6) | For all $n \ge 0$ and $\zeta, b \ge 1$ ($k = \zeta b$), $\Omega_{\zeta,b}$ satisfies Definition 1.2 at $\eta = \frac{5\zeta^4}{2k} = O(\zeta^4/k)$ with probability $\ge 9/10$. |
| 5 | `Theorem_2_2_FlatPreservation` | Theorem 2.2 (pp. 10, 24) | Uniform preservation of $(m, \varepsilon)$-flat unit vectors for arbitrary $\varepsilon, \delta_{\mathrm{loc}} \in (0,1)$ with universal linear scaling $\lambda \ge c_\lambda \varepsilon$ ($c_\lambda > 0$): $\Pr[\exists x \in S^{r-1},\; d_m(Qx) \ge \varepsilon \wedge \|\Omega^\top Q x\|_2 < \lambda] \le \delta_{\mathrm{loc}}$. |
| 6 | `Theorem_2_3_CommonSupport` | Theorem 2.3 (pp. 11, 28) | Deterministic spiky common-support extraction: if all $(m, \varepsilon)$-flat unit images satisfy $\|X x\|_2 \ge \lambda$, then $\exists I \subseteq [n]$ with $|I| \le 8m$ and $Q_{I^c}^\top Q_{I^c} \preceq \frac{8}{3}\varepsilon^2 I_r + \frac{8}{3\lambda^2} X^\top X$. |
| 7 | `Lemma_2_4_IsolatedCrossTerm` | Lemma 2.4 (pp. 12, 29, 33) | Conditional expectation of $\|\tilde{\Omega}_I \tilde{\Omega}_{I^c}^\top V\|$ given $\Omega_I = \omega_0$ for $b \ge 2\zeta$, $p \ge \max\{1, \log(2d)\}$, and ambient off-$I$ isometry $V \in \mathbb{R}^{n \times d}$, plus exact vanishing at $I = \emptyset$ or $d = 0$. |
| 8 | `Lemma_2_4_IsolatedCrossTerm_Submatrix` | Lemma 2.4 / Lemma 5.5 (pp. 12, 29, 33) | Exact $|I| \times d$ submatrix form $\mathbb{E}[\|\tilde{\Omega}_I \tilde{\Omega}_J^\top W\| \mid \Omega_I = \omega_0]$ for arbitrary disjoint $I, J \subseteq [n]$ and $W \in \mathbb{R}^{|J| \times d}$ ($W^\top W = I_d$). |
| 9 | `Theorem_2_5_HeavyPreservation` | Theorem 2.5 (pp. 14, 38–39) | Heavy-coordinate preservation for **all** integers $\zeta \ge C_\star \sqrt{\log(e r)}$, $k = \zeta b \ge K_\star r$, $t_0 \in (0, 1/4)$, $\delta_{\mathrm{rep}} \in (0,1)$, $|I| \le \min\{r, b/16\}$ ($\beta \ge \frac{1}{3}(\frac{11}{12} - 2t_0) > 0$): both Rayleigh and Loewner forms hold w.p. $\ge 1 - \delta_{\mathrm{rep}}$. |
| 10 | `Theorem_2_5_HeavyPreservation_EvenBlocks` | Theorem 2.5 proof (pp. 38–39, line 2438) | Exact printed constant $\beta = \frac{11}{24} - t_0 > 0$ when $\zeta = 2\zeta_1$ splits into two equal $\zeta_1$-block groups. |
| 11 | `Fact_3_1_McDiarmid` | Fact 3.1 `[McD89]` (p. 20, Eq. (17)) | Proved from scratch (`0` custom axioms) for arbitrary independent finite-space coordinates: both upper and lower tails $\le \exp(-2t^2 / \sum_{i=1}^N c_i^2)$. |
| 12 | `Lemma_3_2_WeightedBernoulli` | Lemma 3.2 proof (pp. 22–23) | Weighted independent Bernoulli lower-tail bound $\Pr[\sum_j v_j B_j < c_1 V_0] \le \exp(-c_2 V_0 / v_{\max})$ for general $p_0 > 0$ over arbitrary `MeasureTheory.Measure`. |
| 13 | `Lemma_3_2_PointwiseFlat` | Lemma 3.2 (p. 20) | Pointwise small-ball bound for $h + a z$ ($\operatorname{supp}(h) \cap \operatorname{supp}(z) = \emptyset$, $\|z\|_2 = 1$, $\|z\|_\infty^2 \le D^{-1}$, $1 \le D \le b$): $\Pr[\|\Omega^\top(h + a z)\|_2 < c_0 a] \le 2 e^{-c_{\mathrm{sb}} \zeta D}$. |
| 14 | `Lemma_3_3_LatticeRounding` | Lemma 3.3 (p. 23) | Unbiased lattice rounding net $N_\eta \subset (1+\eta) B_2^r$ of size $\le (16/\eta)^r$ achieving $\|x - y\|_2 \le \eta$ and $\|T(x-y)\|_2^2 \le \frac{\eta^2}{4r}\|T\|_F^2$ simultaneously for every $T \in \mathbb{R}^{k \times r}$. |
| 15 | `Lemma_4_1_GaussianTruncation` | Lemma 4.1 (p. 26) | Expected squared $m$-tail $\mathbb{E}[d_m(g)^2] \ge \frac{3}{4} \sum_{i > 4m} a_{\sigma(i)}$ for any random vector $g$ ($n > 4m$) with marginal fourth-moment bound $\mathbb{E}[g_i^4] \le 3(\mathbb{E}[g_i^2])^2$ (including all centered Gaussians). |
| 16 | `Lemma_4_2_MinimaxSelection` | Lemma 4.2 (p. 27) | Minimax common-coordinate extraction: $d_m(Vx)^2 \le x^\top H x$ ($H \succeq 0$) $\implies \exists |I| \le 8m,\; V_{I^c}^\top V_{I^c} \preceq \frac{8}{3} H$. |
| 17 | `Claim_4_3_MinimaxWeights` | Claim 4.3 (p. 27, Eqs. (22)–(25)) | Both (1) minimax duality ($\forall R \succeq 0$ with $\operatorname{tr} R = 1$, $\exists w \in \mathcal{W}$ with $\operatorname{tr}(R(D(w) - \frac{4}{3}H)) \le 0 \implies \exists w \in \mathcal{W},\; D(w) \preceq \frac{4}{3}H$) and (2) existence of $w \in \mathcal{W}_{4m}$ under $d_m(Vx)^2 \le x^\top H x$. |
| 18 | `Fact_5_1_HeidaryOffDiagMoment` | Fact 5.1 `[Hei26]` (p. 30, Eq. (27)) | Proved without axioms via vendored `SparseFockFormal`: $\mathbb{E}[\operatorname{tr}(F^{2p})] \le d [3(3+\sqrt{2})(\sqrt{D_p/m} + D_p/m + (2p+1)/a)]^{2p}$. |
| 19 | `Fact_5_2_ScalarVarMatrixBernstein` | Fact 5.2 (pp. 30–31, Eq. (28)) | Proved from scratch via Golden–Thompson + 2-function MVT (see Subtlety 4 below): $\mathbb{E}[\|\sum_j R_j\|] \le \sqrt{2 v \log(2d)} + \frac{\ell}{3}\log(2d)$ under scalar variance proxies $\mathbb{E}[R_j^2] \preceq v_j I_d$. |
| 20 | `Lemma_5_3_IidOpNorm` | Lemma 5.3 (p. 31) | Independent-entry $\{\pm 1, 0\}$ operator-norm second moment $\mathbb{E}[\|X W\|^2] \le C_{\mathrm{ind}}(a + D_p/B + p)$ for all $B \ge 2, a \ge 1, d \ge 1, p \ge \max\{1, \log(2d)\}$. |
| 21 | `Claim_5_4_SingleBlockCoupling` | Claim 5.4 (p. 32, Eq. (31)) | Explicit joint PMF $J$ on $\{-1,0,1\}^b \times ([b] \times \{\pm 1\})$ with exact marginals, $1 \le c_b = (1-(1-1/b)^b)^{-1} \le (1-e^{-1})^{-1} < 2$, and $\mathbb{E}[\eta \mid \xi] = c_b^{-1} \xi$. |
| 22 | `Lemma_5_5_CouplingJensen` | Lemma 5.5 (p. 32, Eq. (32)) | Conditional Jensen coupling bound $\mathbb{E}[\|\tilde{\Omega}_I \tilde{\Omega}_J^\top W\| \mid \Omega_{\zeta,b,I} = \omega_0] \le c_b \mathbb{E}[\|U W\|]$ for all $\zeta, b \ge 1$ and disjoint $I, J \subseteq [n]$. |
| 23 | `Claim_5_6_SymmetricConvexDom` | Claim 5.6 (p. 34, Eq. (42)) | Symmetric bounded convex dominance $\mathbb{E}[\varphi(V)] \le \mathbb{E}[\varphi(2\eta_B)] = (1 - \frac{1}{B})\varphi(0) + \frac{1}{2B}(\varphi(2)+\varphi(-2))$ for $|V| \le 2$, $\mathbb{E}[|V|] \le 1/B$, and every convex $\varphi : \mathbb{R} \to \mathbb{R}$. |
| 24 | `Lemma_5_7_FullSketchMoment` | Lemma 5.7 (p. 35, Eq. (47)) | Full SparseStack Gram error $2p$-th moment bound with the **exact printed constant** $C_{\mathrm{mom}} = 12(3 + \sqrt{2})$. |
| 25 | `Theorem_Def61_Def62_Equivalence` | Definitions 6.1 & 6.2 (p. 36) | Exact equivalence between matrix-entry definitions (`landsInBucket`, `IsIsolatedBucket`, `landedBuckets`, `isolatedLandedBuckets`, `IsGoodCoordMatrix`) on $\Omega_{\zeta,b,S}^\top$ and combinatorial `bucketLoad` / `isolatedBlockCount`. |
| 26 | `Lemma_6_3_SingleGroup` | Lemma 6.3 (p. 36, Eq. (49)) | **Unconditional** single-group norm preservation exactly as printed in Lemma 6.3 (no upper cap on $\zeta$, no $b \ge 2\zeta$ hypothesis, literal `IsGoodCoordMatrix` from Defs. 6.1–6.2; see Subtlety 2 below). |
| 27 | `Lemma_6_3_SingleGroup_Conditional` | Lemma 6.3 proof (p. 36) | Conditional-on-$\Omega_S$ moderate-sparsity form ($\zeta_0 \le H_0 \log(eR)$, $b \ge 2\zeta_0$, conditioned on any fixed head realization $\omega_0$). |
| 28 | `Lemma_6_4_TwoGroupIsolation` | Lemma 6.4 (pp. 37–38) | Two-group balls-into-bins isolation at Kijun's **exact printed constant $c_1 = 1/2304$** in both parts (i) and (ii) (for all $r \ge 2, b \ge 1, |I| \le \min\{r, b/16\}$). |

---

## 3. Six Concrete Mathematical Subtleties Uncovered in `constant_injectivity_sparsestack-2.pdf`

During formalization of Kijun's revised manuscript, six subtle mathematical points in the prose proofs were identified and resolved rigorously in Lean:

1. **Lemma 6.4 (p. 38, lines 2345–2352) — McDiarmid Coordinate Granularity & Group-2 Binomial MGF:**
   - On p. 38, Kijun's updated manuscript fixes the constant from $1/1152$ to **$c_1 = 1/2304$** so $\exp(-2(\frac{1}{48})^2 \zeta_1) = e^{-2 c_1 \zeta_1}$ is algebraically exact, and writes: *"Changing a single column index in block $t$ alters $a_i$ by at most $1$. Applying McDiarmid's inequality (Fact 3.1) gives $\mathbb{P}[a_i < \frac{11}{12}\zeta_1] \le \exp(-2(\frac{1}{48})^2 \zeta_1) = e^{-2 c_1 \zeta_1}$."*
   - **Subtlety:** Fact 3.1 must be applied to the **$\zeta_1$ independent block hash-tuples** $Z_t = (s_{j,t})_{j \in I}$ ($t \in [\zeta_1]$, bounded difference $1$ per block, so $\sum_{t=1}^{\zeta_1} c_t^2 = \zeta_1$), *not* to the $\zeta_1 |I|$ individual column-block hashes $(j, t) \in I \times [\zeta_1]$ (changing any $j \ne i$ in block $t$ can also change $a_i$ by $1$, which would yield $\sum c_{j,t}^2 = \zeta_1 |I|$ and lose a factor of $|I|$ in the exponent!).
   - Furthermore, Part (ii) of Lemma 6.4 crucially relies on the **super-exponential** Group-2 collision MGF $(e^{-c_1 \zeta_1}/16)^{\zeta_1/12} = e^{-\Omega(\zeta_1^2)}$ when union-bounding over $|B| \le r$ coordinates (since $r e^{-\Theta(\zeta_1)}$ would fail at $\zeta_1 = \Theta(\sqrt{\log r})$). Both parts hold verbatim at Kijun's exact $c_1 = 1/2304$ (`Lemma_6_4_TwoGroupIsolation`).

2. **Lemma 6.3 (p. 36, lines 2243–2277) — Unconditional Statement vs. Moderate-Sparsity Proof:**
   - Kijun states Lemma 6.3 unconditionally for **all** $\zeta \ge C_0 \sqrt{\log(e r)}$ and $k = \zeta b \ge K_0 r$ ($b \ge 2$), without assuming $\zeta = O(\log r)$ or $b \ge 2\zeta$.
   - However, the prose proof on p. 36 invokes Lemma 2.4 directly: Lemma 2.4 requires $b \ge 2\zeta$ (i.e. $k = \zeta b \ge 2\zeta^2$) and has second error term $\sqrt{|S| d \binom{\zeta}{3} / (\zeta^2 b^3)} \asymp \sqrt{r^2 \zeta^4 / k^3}$, which **diverges** when $k = \Theta(r)$ and $\zeta \gg r^{1/4}$!
   - **Resolution:** Unconditional Lemma 6.3 **is** true as stated! In `OsiUb/UpperBound/Sec6.lean`, we split at $\zeta < H_{\mathrm{sg}} \log(e r)$ vs. $\zeta \ge H_{\mathrm{sg}} \log(e r)$:
     - When $\zeta < H_{\mathrm{sg}} \log(e r)$, choosing $K_0 \ge 2 H_{\mathrm{sg}}^2$ forces $\zeta b \ge K_0 r > 2\zeta^2$ (hence $b \ge 2\zeta$), and Lemma 2.4 gives the conditional-on-$\Omega_S$ bound (`Lemma_6_3_SingleGroup_Conditional`).
     - When $\zeta \ge H_{\mathrm{sg}} \log(e r)$, applying full-sketch moment Lemma 5.7 to the joint $(|S| + d \le 3r)$-column isometry $U = [I_S, W]$ gives $\|U^\top \Omega \Omega^\top U - I_D\| \le 1/12$ w.p. $\ge 1 - \delta_{\mathrm{rep}}/4$, hence $\|\Omega_S^\top h + \Omega_{S^c}^\top W f\|^2 + t\|f\|^2 \ge \frac{11}{12}(\|h_G\|^2 + \|h_B\|^2 + \|f\|^2) + t\|f\|^2 \ge (\frac{11}{12} - t)\|h_G\|^2 - t\|h_B\|^2$ unconditionally! Both `Lemma_6_3_SingleGroup` (unconditional, with literal `IsGoodCoordMatrix`) and `Lemma_6_3_SingleGroup_Conditional` are proved.

3. **Lemma 2.4 & Claim 5.6 (pp. 33–34, lines 2093–2139) — Integer Floor Parameters & Factor-of-2 Slack:**
   - On p. 34, Kijun writes integer parameters $B = b/\zeta \ge 2$ and $a = N/B + 1 \ge 1$ without floor brackets; in Lean (`SparseStack/CrossGram.lean`), setting $B = \lfloor b/\zeta \rfloor \ge 2$ (valid since $b \ge 2\zeta$) and $a = \lfloor N/B \rfloor + 1 \ge 1$ satisfies $N \le a B$, $1/B \le 2\zeta / b$, and $a \le N/B + 1$ cleanly. Also in Eqs. (44)–(45), $\mathbb{P}(V \ne 0) \le \zeta / b \le 1/B$ (with $|V| \le 2$ symmetric, so $\mathbb{E}[|V|]/2 \le 1/B$), matching Claim 5.6's hypothesis cleanly.

4. **Fact 5.2 & Lemma 5.3 (pp. 30–31, lines 1830–1883) — Scalar-Variance Matrix Bernstein:**
   - Tropp's general Matrix Bernstein inequality (`Fact 5.2` with arbitrary matrix variance $\sigma^2 = \|\sum_j \mathbb{E}[R_j^2]\|$) classically requires **Lieb's concavity theorem** (not yet in Mathlib), whereas when each independent summand has a **scalar** variance upper bound $\mathbb{E}[R_j^2] \preceq v_j I_d$ ($\sum_j v_j \le v$), Golden–Thompson $\operatorname{tr} e^{A+B} \le \operatorname{tr}(e^A e^B)$ suffices!
   - Crucially, in Lemma 5.3's proof (p. 31, line 1865), grouping the diagonal summands by **row** $R_\ell = \sum_{j=1}^n a^{-1}(X_{\ell,j}^2 - B^{-1}) w_j w_j^\top$ ($\ell \in [m]$) preserves $\|R_\ell\| \le a^{-1}$ (since $\sum_j w_j w_j^\top = W^\top W = I_d$ and $|X_{\ell,j}^2 - B^{-1}| \le 1$) and gives **exact scalar per-row variance** $\mathbb{E}[R_\ell^2] \preceq (B a^2)^{-1} I_d$ with $\sum_{\ell=1}^{aB} (B a^2)^{-1} = a^{-1}$! We prove `Fact_5_2_ScalarVarMatrixBernstein` from scratch in `OsiUb/UpperBound/Sec5.lean` (`0` axioms).

5. **Theorem 2.5 (pp. 14, 38–39) — Parity of Block Count $\zeta$:**
   - Splitting $\zeta$ into two equal $\zeta_1 = \zeta/2$ groups yields the exact printed constant $\beta = \frac{11}{24} - t_0$ when $\zeta = 2\zeta_1$ is even (`Theorem_2_5_HeavyPreservation_EvenBlocks`), while for arbitrary integer $\zeta$ (possibly odd), taking two disjoint $\lfloor \zeta/2 \rfloor$-block groups and dropping any leftover block by PSD monotonicity yields $\beta = \rho_0(\frac{11}{12} - 2t_0) \ge \frac{1}{3}(\frac{11}{12} - 2t_0) > 0$ (`Theorem_2_5_HeavyPreservation`).

6. **Lemma 2.4 Notation $\tilde{\Omega}_{I^c}^\top W$ vs. $W \in \mathbb{R}^{|J| \times d}$ (pp. 12, 29, 33):**
   - Lemma 2.4 writes $W \in \mathbb{R}^{|J| \times d}$ ($I, J \subseteq [n]$ disjoint) in its hypothesis and $\tilde{\Omega}_I \tilde{\Omega}_{I^c}^\top W$ in Eq. (14) (and $\tilde{\Omega}_I \tilde{\Omega}_J^\top W$ in Lemma 5.5 Eq. (32)). Both formulations are formalized and proved (`Lemma_2_4_IsolatedCrossTerm` and `Lemma_2_4_IsolatedCrossTerm_Submatrix`), bridged via zero-padding `embedSubmatrix J W`.

---

## 4. Scope Boundary (Upper Bound Only)

- Per the request (*"generate Lean proof for the UB side"*), `OsiUb/Spec.lean` covers **Sections 1–7 (pp. 1–40)** of `constant_injectivity_sparsestack-2.pdf` in full (`28` UB statements + `AllUpperBoundTheorems`).
- The Lower-Bound side (Theorem 1.3 and Sections 8–10, pp. 40–55) and the cited `[CEMT25]` regression / column-subset-selection corollaries in Section 1.2 (pp. 7–8) are outside the scope of `OsiUb`.
