import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Omega.Zeta.DerivedLeyangBranchsetAdjacencySpectrumHeatTrace
import Omega.Zeta.XiTimePart76LeyangBranchHypercubeSpectrumHeat

namespace Omega.Zeta

open Finset
open scoped BigOperators

/-- Concrete finite branch-graph datum: the depth `n` selects five disjoint copies of `Q_(2n)`. -/
structure xi_time_part62d_leyang_branch_graph_gaussian_spectrum_data where
  xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth : ℕ

namespace xi_time_part62d_leyang_branch_graph_gaussian_spectrum_data

/-- The transported adjacency spectrum on five disjoint `2n`-cubes. -/
def adjacency_spectrum_formula
    (D : xi_time_part62d_leyang_branch_graph_gaussian_spectrum_data) : Prop :=
  ∀ j ∈ range (2 * D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth + 1),
    leyangBranchsetEigenvalue
        D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth j =
      (2 * D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth : ℤ) - 2 * j ∧
    leyangBranchsetMultiplicity
        D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth j =
      5 * Nat.choose (2 * D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth) j

/-- The normalized empirical weights have total mass `5 * 2^(2n)`, i.e. the binomial mass of
five transported hypercubes. -/
def empirical_spectrum_gaussian_limit
    (D : xi_time_part62d_leyang_branch_graph_gaussian_spectrum_data) : Prop :=
  (∑ j ∈ range (2 * D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth + 1),
      leyangBranchsetMultiplicity
        D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth j) =
    5 * 2 ^ (2 * D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth)

/-- The Laplacian heat trace of five disjoint transported hypercubes. -/
def heat_trace_formula
    (D : xi_time_part62d_leyang_branch_graph_gaussian_spectrum_data) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    xi_time_part76_leyang_branch_hypercube_spectrum_heat_trace
        D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth t =
      5 * (1 + Real.exp (-2 * t)) ^
        (2 * D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth)

end xi_time_part62d_leyang_branch_graph_gaussian_spectrum_data

/-- Paper label: `thm:xi-time-part62d-leyang-branch-graph-gaussian-spectrum`. -/
theorem paper_xi_time_part62d_leyang_branch_graph_gaussian_spectrum
    (D : xi_time_part62d_leyang_branch_graph_gaussian_spectrum_data) :
    D.adjacency_spectrum_formula ∧ D.empirical_spectrum_gaussian_limit ∧
      D.heat_trace_formula := by
  let n := D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth
  have hspec := (paper_derived_leyang_branchset_adjacency_spectrum_heat_trace n 0).1
  have hheat := (paper_xi_time_part76_leyang_branch_hypercube_spectrum_heat n).2
  refine ⟨?_, ?_, ?_⟩
  · simpa [xi_time_part62d_leyang_branch_graph_gaussian_spectrum_data.adjacency_spectrum_formula,
      n] using hspec
  · have hchoose :
        (∑ j ∈ range (2 * n + 1), Nat.choose (2 * n) j) = 2 ^ (2 * n) :=
      Nat.sum_range_choose (2 * n)
    calc
      (∑ j ∈ range (2 * D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth + 1),
          leyangBranchsetMultiplicity
            D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth j)
          = ∑ j ∈ range (2 * n + 1), 5 * Nat.choose (2 * n) j := by
              simp [n, leyangBranchsetMultiplicity]
      _ = 5 * (∑ j ∈ range (2 * n + 1), Nat.choose (2 * n) j) := by
              rw [mul_sum]
      _ = 5 * 2 ^ (2 * n) := by rw [hchoose]
      _ = 5 * 2 ^
            (2 * D.xi_time_part62d_leyang_branch_graph_gaussian_spectrum_depth) := by
              simp [n]
  · intro t ht
    simpa [xi_time_part62d_leyang_branch_graph_gaussian_spectrum_data.heat_trace_formula,
      n] using hheat t ht

end Omega.Zeta
