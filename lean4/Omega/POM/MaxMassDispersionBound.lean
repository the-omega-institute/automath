import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic

/-! ### Max mass upper bound by dispersion index

For a positive distribution w on a finite set X with |X| = n, the dispersion
index D(w) = (1/n²) Σ (1/w(x)) satisfies a Cauchy-Schwarz lower bound
involving the maximum mass w_max. This gives a deterministic upper bound
on the largest probability mass via the dispersion index.

cor:pom-max-mass-upper-bound-by-dispersion -/

namespace Omega.POM

/-- Paper seed: numerical verification for window-6.
    |X_6| = 21, d_max = 4, so w_max = 4/64 = 1/16.
    The dispersion bound gives: 1/(1/16) + 20²/(1 - 1/16) = 16 + 6400/15.
    cor:pom-max-mass-upper-bound-by-dispersion -/
theorem paper_dispersion_max_mass_seed_window6 :
    (21 : ℚ) - 3 = 18 ∧
    (4 : ℚ) / 64 = 1 / 16 ∧
    (1 : ℚ) / (1 / 16) + (21 - 1) ^ 2 / (1 - 1 / 16) =
      16 + 6400 / 15 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/-- Paper seed: the weak form of the max mass upper bound.
    w_max ≤ 1 - (n-1)²/(n² · D) when n² · D > (n-1)².
    Numerical check for n = 21, D = 2 (conservative estimate).
    cor:pom-max-mass-upper-bound-by-dispersion -/
theorem paper_max_mass_upper_bound_weak_seed :
    (1 : ℚ) - (21 - 1) ^ 2 / (21 ^ 2 * 2) = 1 - 400 / 882 ∧
    (400 : ℚ) / 882 = 200 / 441 ∧
    (1 : ℚ) - 200 / 441 = 241 / 441 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/-- Core rearrangement: if (n-1)²/((1 - wmax) · n²) ≤ D then
    wmax ≤ 1 - (n-1)²/(n² · D). This is the algebraic content
    of the max mass upper bound by dispersion.
    cor:pom-max-mass-upper-bound-by-dispersion -/
theorem paper_max_mass_rearrangement (n : ℕ) (D wmax : ℝ)
    (hn : 2 ≤ n) (hD : 0 < D) (_hwmax : 0 < wmax) (hwmax1 : wmax < 1)
    (hbound : (↑n - 1) ^ 2 ≤ D * ((↑n) ^ 2 * (1 - wmax))) :
    wmax ≤ 1 - (↑n - 1) ^ 2 / ((↑n) ^ 2 * D) := by
  have hn' : (0 : ℝ) < n := by positivity
  have hn2 : (0 : ℝ) < (↑n) ^ 2 := by positivity
  have h1w : 0 < 1 - wmax := by linarith
  have hDn : 0 < (↑n) ^ 2 * D := mul_pos hn2 hD
  have hle : (↑n - 1) ^ 2 / (↑n ^ 2 * D) ≤ 1 - wmax := by
    rw [div_le_iff₀ hDn]
    linarith
  linarith

/-- Cauchy-Schwarz gives: for k positive reals summing to S,
    Σ(1/w_i) ≥ k²/S. Numerical seed for k=20, S = 15/16.
    cor:pom-max-mass-upper-bound-by-dispersion -/
theorem paper_cauchy_schwarz_reciprocal_seed :
    (20 : ℚ) ^ 2 / (15 / 16) = 6400 / 15 := by norm_num

/-- Combined: 1/w_max + (n-1)²/(1 - w_max) is a lower bound for n² · D(w).
    Seed for the paper statement with rational arithmetic.
    cor:pom-max-mass-upper-bound-by-dispersion -/
theorem paper_dispersion_combined_lower_bound_seed :
    ∀ n : ℕ, 2 ≤ n →
      (1 : ℚ) / (1 / n) + (↑n - 1) ^ 2 / (1 - 1 / ↑n) = ↑n + (↑n - 1) ^ 2 * ↑n / (↑n - 1) := by
  intro n hn
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (n : ℚ) - 1 ≠ 0 := by
    have : (1 : ℚ) < n := by exact_mod_cast hn
    linarith
  field_simp

end Omega.POM
