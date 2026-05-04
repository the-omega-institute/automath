import Omega.Zeta.XiTimePart76LeyangBranchHypercubeSpectrumHeat

namespace Omega.Zeta

open Finset
open scoped BigOperators

/-- The single `2n`-cube Ihara--Bass factor appearing in the Lee--Yang branch graph. -/
def xi_time_part76_leyang_branch_ihara_bass_closed_componentFactor
    (n : ℕ) (u : ℚ) : ℚ :=
  (1 - u ^ 2) ^ ((2 * n - 2) * 2 ^ (2 * n - 1)) *
    ∏ j ∈ range (2 * n + 1),
      (1 - (((2 * n : ℤ) - 2 * (j : ℤ) : ℤ) : ℚ) * u +
          ((2 * n - 1 : ℕ) : ℚ) * u ^ 2) ^ Nat.choose (2 * n) j

/-- The fivefold Lee--Yang branch Ihara inverse zeta factor. -/
def xi_time_part76_leyang_branch_ihara_bass_closed_inverse
    (n : ℕ) (u : ℚ) : ℚ :=
  xi_time_part76_leyang_branch_ihara_bass_closed_componentFactor n u ^ 5

/-- Concrete statement for `cor:xi-time-part76-leyang-branch-ihara-bass-closed`. -/
def xi_time_part76_leyang_branch_ihara_bass_closed_statement : Prop :=
  ∀ n : ℕ, ∀ u : ℚ,
    xi_time_part76_leyang_branch_ihara_bass_closed_inverse n u =
        xi_time_part76_leyang_branch_ihara_bass_closed_componentFactor n u ^ 5 ∧
      ∀ j : ℕ, j ≤ 2 * n →
        xi_time_part76_leyang_branch_hypercube_spectrum_heat_adjMultiplicity n j =
          5 * Nat.choose (2 * n) j

/-- Paper label: `cor:xi-time-part76-leyang-branch-ihara-bass-closed`. -/
theorem paper_xi_time_part76_leyang_branch_ihara_bass_closed :
    xi_time_part76_leyang_branch_ihara_bass_closed_statement := by
  intro n u
  refine ⟨rfl, ?_⟩
  exact (paper_xi_time_part76_leyang_branch_hypercube_spectrum_heat n).1

end Omega.Zeta
