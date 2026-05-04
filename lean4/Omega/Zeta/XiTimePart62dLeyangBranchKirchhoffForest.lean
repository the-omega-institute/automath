import Mathlib.Tactic
import Omega.Zeta.DerivedLeyangBranchsetAdjacencySpectrumHeatTrace
import Omega.Zeta.XiHypercubeWeightedSpanningTreeSpectrumProduct

namespace Omega.Zeta

open scoped BigOperators

/-- The single Lee--Yang branch component uses the unweighted `2n`-cube Kirchhoff product. -/
noncomputable def xi_time_part62d_leyang_branch_kirchhoff_forest_componentProduct
    (n : ℕ) : ℝ :=
  xi_hypercube_weighted_spanning_tree_spectrum_product_treeWeight
    (k := 2 * n) (fun _ : Fin (2 * n) => (1 : ℝ))

/-- Five independent Lee--Yang branch components multiply the component forest product. -/
noncomputable def xi_time_part62d_leyang_branch_kirchhoff_forest_fiveComponentProduct
    (n : ℕ) : ℝ :=
  xi_time_part62d_leyang_branch_kirchhoff_forest_componentProduct n ^ 5

/-- Label-prefixed Kirchhoff forest statement for five Lee--Yang branch hypercubes. -/
def xi_time_part62d_leyang_branch_kirchhoff_forest_statement : Prop :=
  ∀ n : ℕ,
    xi_time_part62d_leyang_branch_kirchhoff_forest_componentProduct n =
        (2 : ℝ) ^ (2 ^ (2 * n) - (2 * n) - 1) *
          Finset.prod
            (xi_hypercube_weighted_spanning_tree_spectrum_product_nonemptySubsets (2 * n))
            (fun S => Finset.sum S (fun _ : Fin (2 * n) => (1 : ℝ))) ∧
      xi_time_part62d_leyang_branch_kirchhoff_forest_fiveComponentProduct n =
        ((2 : ℝ) ^ (2 ^ (2 * n) - (2 * n) - 1) *
          Finset.prod
            (xi_hypercube_weighted_spanning_tree_spectrum_product_nonemptySubsets (2 * n))
            (fun S => Finset.sum S (fun _ : Fin (2 * n) => (1 : ℝ)))) ^ 5 ∧
      (∀ j ∈ Finset.range (2 * n + 1),
        leyangBranchsetEigenvalue n j = (2 * n : ℤ) - 2 * j ∧
          leyangBranchsetMultiplicity n j = 5 * Nat.choose (2 * n) j)

/-- Paper label: `thm:xi-time-part62d-leyang-branch-kirchhoff-forest`. -/
theorem paper_xi_time_part62d_leyang_branch_kirchhoff_forest :
    xi_time_part62d_leyang_branch_kirchhoff_forest_statement := by
  intro n
  have hcomponent :=
    paper_xi_hypercube_weighted_spanning_tree_spectrum_product
      (2 * n) (fun _ : Fin (2 * n) => (1 : ℝ)) (by intro i; positivity)
  have hspectrum :=
    (paper_derived_leyang_branchset_adjacency_spectrum_heat_trace n 0).1
  refine ⟨?_, ?_, hspectrum⟩
  · simpa [xi_time_part62d_leyang_branch_kirchhoff_forest_componentProduct] using hcomponent
  · rw [xi_time_part62d_leyang_branch_kirchhoff_forest_fiveComponentProduct,
      xi_time_part62d_leyang_branch_kirchhoff_forest_componentProduct, hcomponent]

end Omega.Zeta
