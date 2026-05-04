import Mathlib

namespace Omega.Zeta

/-- Concrete data for the Lambert-W zero indexing estimate.  The fields keep the analytic
zero-counting estimate, the eventual bracket, and the slope lower bound as real inequalities. -/
structure xi_lambertw_zero_indexing_explicit_data where
  N0 : ℝ → ℝ
  E : ℝ → ℝ
  T : ℕ → ℝ
  gamma : ℕ → ℝ
  n0 : ℕ
  T_eq : ∀ n : ℕ, n0 ≤ n → N0 (T n) = (n : ℝ)
  gamma_bracket : ∀ n : ℕ, n0 ≤ n → T n / 2 ≤ gamma n ∧ gamma n ≤ 2 * T n
  defect_at_gamma :
    ∀ n : ℕ, n0 ≤ n → |N0 (gamma n) - (n : ℝ)| ≤ E (2 * T n) + 1
  slope_pos :
    ∀ n : ℕ, n0 ≤ n → 0 < Real.log (T n / (4 * Real.pi))
  slope_lower :
    ∀ n : ℕ, n0 ≤ n →
      (Real.log (T n / (4 * Real.pi)) / (2 * Real.pi)) * |gamma n - T n| ≤
        |N0 (gamma n) - N0 (T n)|

/-- The advertised explicit absolute-error bound for the zero ordinate indexed by `n`. -/
def xi_lambertw_zero_indexing_explicit_data.statement
    (D : xi_lambertw_zero_indexing_explicit_data) : Prop :=
  ∀ n : ℕ, D.n0 ≤ n →
    |D.gamma n - D.T n| ≤
      2 * Real.pi * (D.E (2 * D.T n) + 1) / Real.log (D.T n / (4 * Real.pi))

/-- Paper label: `thm:xi-lambertW-zero-indexing-explicit`.  Once the zero-counting defect
`|N0(gamma_n)-n|` and the lower slope on the bracket around `T_n` are available, the stated
Lambert-W indexing error is the mean-value/slope inequality. -/
theorem paper_xi_lambertw_zero_indexing_explicit
    (D : xi_lambertw_zero_indexing_explicit_data) : D.statement := by
  intro n hn
  set L : ℝ := Real.log (D.T n / (4 * Real.pi))
  set A : ℝ := D.E (2 * D.T n) + 1
  have hL : 0 < L := by
    simpa [L] using D.slope_pos n hn
  have hslope_pos : 0 < L / (2 * Real.pi) := by
    exact div_pos hL (mul_pos (by norm_num) Real.pi_pos)
  have hdefect : |D.N0 (D.gamma n) - (n : ℝ)| ≤ A := by
    simpa [A] using D.defect_at_gamma n hn
  have hslope :
      (L / (2 * Real.pi)) * |D.gamma n - D.T n| ≤
        |D.N0 (D.gamma n) - (n : ℝ)| := by
    simpa [L, D.T_eq n hn] using D.slope_lower n hn
  have hmul : |D.gamma n - D.T n| * (L / (2 * Real.pi)) ≤ A := by
    calc
      |D.gamma n - D.T n| * (L / (2 * Real.pi))
          = (L / (2 * Real.pi)) * |D.gamma n - D.T n| := by ring
      _ ≤ |D.N0 (D.gamma n) - (n : ℝ)| := hslope
      _ ≤ A := hdefect
  have hdist : |D.gamma n - D.T n| ≤ A / (L / (2 * Real.pi)) := by
    rwa [le_div_iff₀ hslope_pos]
  calc
    |D.gamma n - D.T n| ≤ A / (L / (2 * Real.pi)) := hdist
    _ = 2 * Real.pi * A / L := by
      field_simp [hL.ne', Real.pi_ne_zero]

end Omega.Zeta
