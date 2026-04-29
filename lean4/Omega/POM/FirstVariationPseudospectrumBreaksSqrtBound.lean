import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for the square-root comparison corollary: a non-Perron spectral scale,
the linear amplification slope coming from first variation, and the small residual error. -/
structure pom_first_variation_pseudospectrum_breaks_sqrt_bound_data where
  nonperronRadius : ℕ → ℝ
  amplificationSlope : ℝ
  residualError : ℕ → ℝ

namespace pom_first_variation_pseudospectrum_breaks_sqrt_bound_data

/-- First variation eventually gives a linear lower bound for a non-Perron spectral radius. -/
def first_variation_pseudospectrum_amplifies
    (D : pom_first_variation_pseudospectrum_breaks_sqrt_bound_data) : Prop :=
  0 < D.amplificationSlope ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → D.amplificationSlope * (n : ℝ) ≤ D.nonperronRadius n

/-- The residual is eventually small compared with the gap between the linear scale and
`sqrt n`. -/
def error_little_o_sqrt
    (D : pom_first_variation_pseudospectrum_breaks_sqrt_bound_data) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    Real.sqrt (n : ℝ) + D.residualError n < D.amplificationSlope * (n : ℝ)

/-- Eventually a non-Perron spectral value beats the square-root benchmark, with residual. -/
def eventually_exists_nonperron_above_sqrt
    (D : pom_first_variation_pseudospectrum_breaks_sqrt_bound_data) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    Real.sqrt (n : ℝ) + D.residualError n < D.nonperronRadius n

end pom_first_variation_pseudospectrum_breaks_sqrt_bound_data

/-- Paper label: `cor:pom-first-variation-pseudospectrum-breaks-sqrt-bound`. -/
theorem paper_pom_first_variation_pseudospectrum_breaks_sqrt_bound
    (D : pom_first_variation_pseudospectrum_breaks_sqrt_bound_data)
    (hamp : D.first_variation_pseudospectrum_amplifies)
    (hsmall : D.error_little_o_sqrt) :
    D.eventually_exists_nonperron_above_sqrt := by
  rcases hamp with ⟨_hslope, Namp, hampN⟩
  rcases hsmall with ⟨Nsmall, hsmallN⟩
  refine ⟨max Namp Nsmall, ?_⟩
  intro n hn
  have hamp_le : Namp ≤ n := le_trans (Nat.le_max_left Namp Nsmall) hn
  have hsmall_le : Nsmall ≤ n := le_trans (Nat.le_max_right Namp Nsmall) hn
  exact lt_of_lt_of_le (hsmallN n hsmall_le) (hampN n hamp_le)

end Omega.POM
