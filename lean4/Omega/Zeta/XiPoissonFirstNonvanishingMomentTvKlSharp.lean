import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete Poisson-kernel asymptotic data at the first nonvanishing centered moment. -/
structure xi_poisson_first_nonvanishing_moment_tv_kl_sharp_data where
  xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℕ
  xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m_ne_zero :
    (xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℝ) ≠ 0
  xi_poisson_first_nonvanishing_moment_tv_kl_sharp_moment : ℝ
  xi_poisson_first_nonvanishing_moment_tv_kl_sharp_l1DerivativeNorm : ℝ
  xi_poisson_first_nonvanishing_moment_tv_kl_sharp_fisherIntegral : ℝ
  xi_poisson_first_nonvanishing_moment_tv_kl_sharp_tvLimit : ℝ
  xi_poisson_first_nonvanishing_moment_tv_kl_sharp_klLimit : ℝ
  xi_poisson_first_nonvanishing_moment_tv_kl_sharp_l1DerivativeNorm_eq :
    xi_poisson_first_nonvanishing_moment_tv_kl_sharp_l1DerivativeNorm =
      (2 / (xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℝ) / Real.pi) *
        ∑ k ∈ Finset.range xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m,
          Real.sin
              (((k + 1 : ℕ) : ℝ) * Real.pi /
                ((xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m + 1 : ℕ) : ℝ)) ^
            (xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m + 1)
  xi_poisson_first_nonvanishing_moment_tv_kl_sharp_fisherIntegral_eq :
    xi_poisson_first_nonvanishing_moment_tv_kl_sharp_fisherIntegral =
      (xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℝ) *
        (Nat.factorial (2 * xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m) : ℝ) /
          (((2 * xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m - 1 : ℕ) : ℝ) *
            2 ^ (2 * xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m))
  xi_poisson_first_nonvanishing_moment_tv_kl_sharp_tvLimit_eq :
    xi_poisson_first_nonvanishing_moment_tv_kl_sharp_tvLimit =
      |xi_poisson_first_nonvanishing_moment_tv_kl_sharp_moment| /
          (Nat.factorial xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℝ) *
        xi_poisson_first_nonvanishing_moment_tv_kl_sharp_l1DerivativeNorm
  xi_poisson_first_nonvanishing_moment_tv_kl_sharp_klLimit_eq :
    xi_poisson_first_nonvanishing_moment_tv_kl_sharp_klLimit =
      xi_poisson_first_nonvanishing_moment_tv_kl_sharp_moment ^ 2 /
          (2 * (Nat.factorial xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℝ) ^ 2) *
        xi_poisson_first_nonvanishing_moment_tv_kl_sharp_fisherIntegral

/-- Closed `L^1` constant after substituting the Poisson derivative norm. -/
def xi_poisson_first_nonvanishing_moment_tv_kl_sharp_tv_closed_constant
    (D : xi_poisson_first_nonvanishing_moment_tv_kl_sharp_data) : ℝ :=
  (2 * |D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_moment|) /
      ((D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℝ) * Real.pi *
        (Nat.factorial D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℝ)) *
    ∑ k ∈ Finset.range D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m,
      Real.sin
          (((k + 1 : ℕ) : ℝ) * Real.pi /
            ((D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m + 1 : ℕ) : ℝ)) ^
        (D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m + 1)

/-- Closed KL constant after substituting the Fisher integral. -/
def xi_poisson_first_nonvanishing_moment_tv_kl_sharp_kl_closed_constant
    (D : xi_poisson_first_nonvanishing_moment_tv_kl_sharp_data) : ℝ :=
  D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_moment ^ 2 /
      (Nat.factorial D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℝ) ^ 2 *
    ((D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℝ) *
      (Nat.factorial (2 * D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m) : ℝ) /
        (((2 * D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m - 1 : ℕ) : ℝ) *
          2 ^ (2 * D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m + 1)))

/-- Paper-facing sharp TV/KL asymptotic constants. -/
def xi_poisson_first_nonvanishing_moment_tv_kl_sharp_statement
    (D : xi_poisson_first_nonvanishing_moment_tv_kl_sharp_data) : Prop :=
  D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_tvLimit =
      xi_poisson_first_nonvanishing_moment_tv_kl_sharp_tv_closed_constant D ∧
    D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_klLimit =
      xi_poisson_first_nonvanishing_moment_tv_kl_sharp_kl_closed_constant D

/-- Paper label: `thm:xi-poisson-first-nonvanishing-moment-tv-kl-sharp`. -/
theorem paper_xi_poisson_first_nonvanishing_moment_tv_kl_sharp
    (D : xi_poisson_first_nonvanishing_moment_tv_kl_sharp_data) :
    xi_poisson_first_nonvanishing_moment_tv_kl_sharp_statement D := by
  constructor
  · rw [xi_poisson_first_nonvanishing_moment_tv_kl_sharp_tv_closed_constant,
      D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_tvLimit_eq,
      D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_l1DerivativeNorm_eq]
    field_simp [D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m_ne_zero]
  · rw [xi_poisson_first_nonvanishing_moment_tv_kl_sharp_kl_closed_constant,
      D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_klLimit_eq,
      D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_fisherIntegral_eq]
    ring

end

end Omega.Zeta
