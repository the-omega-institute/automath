import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Zeta.DerivedLeyangBranchsetAdjacencySpectrumHeatTrace

namespace Omega.Zeta

open Finset
open scoped BigOperators

/-- Product certificate for the adjacency characteristic polynomial of five disjoint `2n`-cubes. -/
noncomputable def xi_time_part62d_leyang_branch_adjacency_charpoly_heat_charpoly
    (n : ℕ) : Polynomial ℤ :=
  ∏ j ∈ range (2 * n + 1),
    (Polynomial.X - Polynomial.C ((2 * n : ℤ) - 2 * (j : ℤ))) ^
      (5 * Nat.choose (2 * n) j)

/-- Concrete statement for the Lee--Yang branch adjacency characteristic polynomial and heat trace. -/
def xi_time_part62d_leyang_branch_adjacency_charpoly_heat_statement : Prop :=
  ∀ n : ℕ, ∀ t : ℝ,
    xi_time_part62d_leyang_branch_adjacency_charpoly_heat_charpoly n =
        ∏ j ∈ range (2 * n + 1),
          (Polynomial.X - Polynomial.C ((2 * n : ℤ) - 2 * (j : ℤ))) ^
            (leyangBranchsetMultiplicity n j) ∧
      (∀ j ∈ range (2 * n + 1),
        leyangBranchsetEigenvalue n j = (2 * n : ℤ) - 2 * j ∧
          leyangBranchsetMultiplicity n j = 5 * Nat.choose (2 * n) j) ∧
      leyangBranchsetHeatTrace n t = 5 * (2 * Real.cosh t) ^ (2 * n)

/-- Paper label: `thm:xi-time-part62d-leyang-branch-adjacency-charpoly-heat`. -/
theorem paper_xi_time_part62d_leyang_branch_adjacency_charpoly_heat :
    xi_time_part62d_leyang_branch_adjacency_charpoly_heat_statement := by
  intro n t
  have hspectral := paper_derived_leyang_branchset_adjacency_spectrum_heat_trace n t
  refine ⟨?_, hspectral.1, hspectral.2⟩
  simp [xi_time_part62d_leyang_branch_adjacency_charpoly_heat_charpoly,
    leyangBranchsetMultiplicity]

end Omega.Zeta
