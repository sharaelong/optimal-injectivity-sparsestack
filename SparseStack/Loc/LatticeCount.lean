import SparseStack.Loc.Basic

/-!
# Counting the lattice net without volumes (W-LOC)

Measure-free replacement of the volume argument in `lem:rounding` (paper, lines 333–348).
For `v ∈ ℤ^r` with `‖h v‖ ≤ R`, Cauchy–Schwarz gives `∑ |v_i| ≤ L := √r R / h`. Hence, for any
`s > 0`,
`#{v ∈ [-K,K]^r : ‖h v‖ ≤ R} ≤ ∑_{v ∈ [-K,K]^r} e^{s (L - ∑ |v_i|)}
  = e^{s L} (∑_{k=-K}^{K} e^{-s|k|})^r ≤ e^{s L} (1 + 2/s)^r`,
using the geometric series `∑_{j ≥ 1} e^{-s j} = 1/(e^s - 1) ≤ 1/s`.
-/

namespace SparseStack

namespace Loc

/-- `∑_{k=-K}^{K} g(|k|) = g(0) + 2 ∑_{j<K} g(j+1)`. -/
theorem sum_Icc_natAbs (g : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Finset.Icc (-(K : ℤ)) K, g k.natAbs = g 0 + 2 * ∑ j ∈ Finset.range K, g (j + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hset : Finset.Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ) =
        insert (-((K + 1 : ℕ) : ℤ)) (insert ((K + 1 : ℕ) : ℤ) (Finset.Icc (-(K : ℤ)) K)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have h1 : ((K + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(K : ℤ)) K := by
      simp only [Finset.mem_Icc]
      push_cast
      omega
    have h2 : (-((K + 1 : ℕ) : ℤ)) ∉ insert ((K + 1 : ℕ) : ℤ) (Finset.Icc (-(K : ℤ)) K) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      push_cast
      omega
    rw [hset, Finset.sum_insert h2, Finset.sum_insert h1, ih, Finset.sum_range_succ]
    have e1 : (-((K + 1 : ℕ) : ℤ)).natAbs = K + 1 := by omega
    have e2 : ((K + 1 : ℕ) : ℤ).natAbs = K + 1 := by omega
    rw [e1, e2]
    ring

/-- Telescoping identity for the geometric sum. -/
theorem geom_tel (q : ℝ) (K : ℕ) :
    (1 - q) * ∑ j ∈ Finset.range K, q ^ (j + 1) = q - q ^ (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- `∑_{j<K} e^{-s (j+1)} ≤ 1/s`. -/
theorem sum_geom_le (s : ℝ) (hs : 0 < s) (K : ℕ) :
    ∑ j ∈ Finset.range K, Real.exp (-s) ^ (j + 1) ≤ 1 / s := by
  have hq0 : 0 < Real.exp (-s) := Real.exp_pos _
  have hqs : Real.exp (-s) * (1 + s) ≤ 1 := by
    have h1 := Real.add_one_le_exp s
    have h2 : Real.exp (-s) * Real.exp s = 1 := by
      rw [← Real.exp_add]
      simp
    calc Real.exp (-s) * (1 + s) ≤ Real.exp (-s) * Real.exp s :=
          mul_le_mul_of_nonneg_left (by linarith) hq0.le
      _ = 1 := h2
  have hS0 : 0 ≤ ∑ j ∈ Finset.range K, Real.exp (-s) ^ (j + 1) :=
    Finset.sum_nonneg (fun j _ => by positivity)
  have htel := geom_tel (Real.exp (-s)) K
  have hqK : 0 ≤ Real.exp (-s) ^ (K + 1) := by positivity
  have h1 : Real.exp (-s) * (s * ∑ j ∈ Finset.range K, Real.exp (-s) ^ (j + 1)) ≤
      Real.exp (-s) * 1 := by
    have hqs' : Real.exp (-s) * s ≤ 1 - Real.exp (-s) := by linarith
    calc Real.exp (-s) * (s * ∑ j ∈ Finset.range K, Real.exp (-s) ^ (j + 1))
        = (Real.exp (-s) * s) * ∑ j ∈ Finset.range K, Real.exp (-s) ^ (j + 1) := by ring
      _ ≤ (1 - Real.exp (-s)) * ∑ j ∈ Finset.range K, Real.exp (-s) ^ (j + 1) :=
          mul_le_mul_of_nonneg_right hqs' hS0
      _ = Real.exp (-s) - Real.exp (-s) ^ (K + 1) := htel
      _ ≤ Real.exp (-s) * 1 := by linarith
  have h2 : s * ∑ j ∈ Finset.range K, Real.exp (-s) ^ (j + 1) ≤ 1 :=
    le_of_mul_le_mul_left h1 hq0
  rw [le_div_iff₀ hs]
  linarith

/-- One-dimensional lattice sum: `∑_{k=-K}^{K} e^{-s|k|} ≤ 1 + 2/s`. -/
theorem sum_Icc_exp_abs_le (s : ℝ) (hs : 0 < s) (K : ℕ) :
    ∑ k ∈ Finset.Icc (-(K : ℤ)) K, Real.exp (-(s * |(k : ℝ)|)) ≤ 1 + 2 / s := by
  have hconv : ∀ k : ℤ, Real.exp (-(s * |(k : ℝ)|)) = Real.exp (-s) ^ k.natAbs := by
    intro k
    rw [← Real.exp_nat_mul, Nat.cast_natAbs, Int.cast_abs]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun k _ => hconv k)]
  rw [sum_Icc_natAbs (fun j => Real.exp (-s) ^ j) K]
  simp only [pow_zero]
  have h := sum_geom_le s hs K
  have h2 : (2 : ℝ) / s = 2 * (1 / s) := by ring
  rw [h2]
  linarith

/-- Integer vectors `v ∈ [-K, K]^r` whose rescaling `h v` lies in the closed ball of radius
`R`. -/
noncomputable def netIdx (r : ℕ) (h R : ℝ) (K : ℕ) : Finset (Fin r → ℤ) :=
  (Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(K : ℤ)) K)).filter
    (fun v => sqNorm (fun i => h * (v i : ℝ)) ≤ R ^ 2)

/-- Cauchy–Schwarz: an index of the net has `∑ |v_i| ≤ √r R / h`. -/
theorem sum_abs_le_of_mem_netIdx {r : ℕ} {h R : ℝ} (hh : 0 < h) (hR : 0 ≤ R) {K : ℕ}
    {v : Fin r → ℤ} (hv : v ∈ netIdx r h R K) : ∑ i, |(v i : ℝ)| ≤ √(r : ℝ) * R / h := by
  unfold netIdx at hv
  rw [Finset.mem_filter] at hv
  have hsq : ∑ i, (h * (v i : ℝ)) ^ 2 ≤ R ^ 2 := by
    have h1 := hv.2
    rwa [sqNorm_eq_sum_sq] at h1
  have hsum : ∑ i, (v i : ℝ) ^ 2 ≤ (R / h) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity), Finset.sum_mul]
    calc ∑ i, (v i : ℝ) ^ 2 * h ^ 2 = ∑ i, (h * (v i : ℝ)) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ R ^ 2 := hsq
  have hCS : ∑ i, 1 * |(v i : ℝ)| ≤ √(∑ _i : Fin r, (1 : ℝ) ^ 2) * √(∑ i, |(v i : ℝ)| ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ => (1 : ℝ)) (fun i => |(v i : ℝ)|)
  have e1 : ∑ i, 1 * |(v i : ℝ)| = ∑ i, |(v i : ℝ)| := by simp
  have e2 : ∑ _i : Fin r, (1 : ℝ) ^ 2 = r := by simp
  have e3 : ∑ i, |(v i : ℝ)| ^ 2 = ∑ i, (v i : ℝ) ^ 2 := by simp
  rw [e1, e2, e3] at hCS
  calc ∑ i, |(v i : ℝ)| ≤ √(r : ℝ) * √(∑ i, (v i : ℝ) ^ 2) := hCS
    _ ≤ √(r : ℝ) * (R / h) := by
        gcongr
        rw [Real.sqrt_le_left (by positivity)]
        exact hsum
    _ = √(r : ℝ) * R / h := by ring

/-- The lattice count: `#netIdx ≤ e^{s √r R / h} (1 + 2/s)^r` for every `s > 0`. -/
theorem card_netIdx_le (r : ℕ) {h R : ℝ} (hh : 0 < h) (hR : 0 ≤ R) (K : ℕ) {s : ℝ}
    (hs : 0 < s) :
    ((netIdx r h R K).card : ℝ) ≤ Real.exp (s * (√(r : ℝ) * R / h)) * (1 + 2 / s) ^ r := by
  have h1 : ((netIdx r h R K).card : ℝ) ≤
      ∑ v ∈ netIdx r h R K, Real.exp (s * (√(r : ℝ) * R / h - ∑ i, |(v i : ℝ)|)) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro v hv
    rw [Nat.cast_one]
    apply Real.one_le_exp
    have := sum_abs_le_of_mem_netIdx hh hR hv
    exact mul_nonneg hs.le (by linarith)
  have h2 : ∑ v ∈ netIdx r h R K, Real.exp (s * (√(r : ℝ) * R / h - ∑ i, |(v i : ℝ)|)) ≤
      ∑ v ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(K : ℤ)) K),
        Real.exp (s * (√(r : ℝ) * R / h - ∑ i, |(v i : ℝ)|)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · unfold netIdx
      exact Finset.filter_subset _ _
    · intro _ _ _
      exact (Real.exp_pos _).le
  have h3 : ∑ v ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(K : ℤ)) K),
        Real.exp (s * (√(r : ℝ) * R / h - ∑ i, |(v i : ℝ)|)) =
      Real.exp (s * (√(r : ℝ) * R / h)) *
        (∑ k ∈ Finset.Icc (-(K : ℤ)) K, Real.exp (-(s * |(k : ℝ)|))) ^ r := by
    have hfac : ∀ v : Fin r → ℤ, Real.exp (s * (√(r : ℝ) * R / h - ∑ i, |(v i : ℝ)|)) =
        Real.exp (s * (√(r : ℝ) * R / h)) * ∏ i, Real.exp (-(s * |(v i : ℝ)|)) := by
      intro v
      rw [← Real.exp_sum, ← Real.exp_add]
      congr 1
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl (fun v _ => hfac v), ← Finset.mul_sum,
      Finset.sum_prod_piFinset (Finset.Icc (-(K : ℤ)) K)
        (fun (_ : Fin r) (k : ℤ) => Real.exp (-(s * |(k : ℝ)|))),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h4 := sum_Icc_exp_abs_le s hs K
  have h5 : 0 ≤ ∑ k ∈ Finset.Icc (-(K : ℤ)) K, Real.exp (-(s * |(k : ℝ)|)) :=
    Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  calc ((netIdx r h R K).card : ℝ) ≤ Real.exp (s * (√(r : ℝ) * R / h)) *
        (∑ k ∈ Finset.Icc (-(K : ℤ)) K, Real.exp (-(s * |(k : ℝ)|))) ^ r := by
        rw [← h3]
        exact h1.trans h2
    _ ≤ Real.exp (s * (√(r : ℝ) * R / h)) * (1 + 2 / s) ^ r := by
        gcongr

end Loc

end SparseStack
