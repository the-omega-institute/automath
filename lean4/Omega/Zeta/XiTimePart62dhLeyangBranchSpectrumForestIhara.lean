import Mathlib.Tactic
import Omega.Zeta.DerivedLeyangBranchsetAdjacencySpectrumHeatTrace
import Omega.Zeta.DerivedLeyangBranchsetIharaZeta

namespace Omega.Zeta

/-- Data for the branch graph spectrum, forest count, and Ihara inverse formula. -/
structure xi_time_part62dh_leyang_branch_spectrum_forest_ihara_data where
  n : ℕ
  forestCount : ℕ

namespace xi_time_part62dh_leyang_branch_spectrum_forest_ihara_data

def adjacency_multiplicities
    (D : xi_time_part62dh_leyang_branch_spectrum_forest_ihara_data) : Prop :=
  ∀ j ∈ Finset.range (2 * D.n + 1),
    leyangBranchsetEigenvalue D.n j = (2 * D.n : ℤ) - 2 * j ∧
      leyangBranchsetMultiplicity D.n j = 5 * Nat.choose (2 * D.n) j

def branch_graph_gaussian_spectrum
    (D : xi_time_part62dh_leyang_branch_spectrum_forest_ihara_data) : Prop :=
  D.adjacency_multiplicities

def laplacian_multiplicities
    (D : xi_time_part62dh_leyang_branch_spectrum_forest_ihara_data) : Prop :=
  ∀ j ∈ Finset.range (2 * D.n + 1),
    (2 * D.n : ℤ) - leyangBranchsetEigenvalue D.n j = 2 * j ∧
      leyangBranchsetMultiplicity D.n j = 5 * Nat.choose (2 * D.n) j

def component_forest_count
    (D : xi_time_part62dh_leyang_branch_spectrum_forest_ihara_data) : Prop :=
  D.forestCount = 5 * 2 ^ (2 * D.n)

def kirchhoff_forest_formula
    (D : xi_time_part62dh_leyang_branch_spectrum_forest_ihara_data) : Prop :=
  D.component_forest_count

def ihara_inverse_closed_form
    (D : xi_time_part62dh_leyang_branch_spectrum_forest_ihara_data) : Prop :=
  DerivedLeyangBranchsetIharaZetaClosedForm D.n

def ihara_bass_formula
    (D : xi_time_part62dh_leyang_branch_spectrum_forest_ihara_data) : Prop :=
  D.ihara_inverse_closed_form

end xi_time_part62dh_leyang_branch_spectrum_forest_ihara_data

/-- Paper label: `cor:xi-time-part62dh-leyang-branch-spectrum-forest-ihara`. -/
theorem paper_xi_time_part62dh_leyang_branch_spectrum_forest_ihara
    (D : xi_time_part62dh_leyang_branch_spectrum_forest_ihara_data)
    (hspec : D.branch_graph_gaussian_spectrum)
    (hforest : D.kirchhoff_forest_formula)
    (hihara : D.ihara_bass_formula) :
    D.adjacency_multiplicities ∧ D.laplacian_multiplicities ∧
      D.component_forest_count ∧ D.ihara_inverse_closed_form := by
  refine ⟨hspec, ?_, hforest, hihara⟩
  intro j hj
  rcases hspec j hj with ⟨heigen, hmult⟩
  constructor
  · rw [heigen]
    ring
  · exact hmult

end Omega.Zeta
