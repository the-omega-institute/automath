import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Omega.Zeta.XiHypercubeWeightedLaplacianHeatTraceFactorization

namespace Omega.Zeta

open scoped BigOperators

/-- Weighted spanning-tree product written in the closed form predicted by the
weighted hypercube Laplacian spectrum. -/
noncomputable def xi_hypercube_weighted_spanning_tree_spectrum_product_nonemptySubsets
    (k : ℕ) : Finset (Finset (Fin k)) :=
  ((Finset.univ : Finset (Fin k)).powerset.erase (∅ : Finset (Fin k)))

/-- Weighted spanning-tree product written in the closed form predicted by the
weighted hypercube Laplacian spectrum. -/
noncomputable def xi_hypercube_weighted_spanning_tree_spectrum_product_treeWeight
    {k : ℕ} (w : Fin k → ℝ) : ℝ :=
  (2 : ℝ) ^ (2 ^ k - k - 1) *
    Finset.prod
      (xi_hypercube_weighted_spanning_tree_spectrum_product_nonemptySubsets k)
      (fun S => Finset.sum S w)

/-- Paper label: `thm:xi-hypercube-weighted-spanning-tree-spectrum-product`. -/
theorem paper_xi_hypercube_weighted_spanning_tree_spectrum_product
    (k : ℕ) (w : Fin k → ℝ) (_hw : ∀ i, 0 < w i) :
    xi_hypercube_weighted_spanning_tree_spectrum_product_treeWeight w =
      (2 : ℝ) ^ (2 ^ k - k - 1) *
        Finset.prod
          (xi_hypercube_weighted_spanning_tree_spectrum_product_nonemptySubsets k)
          (fun S => Finset.sum S w) := by
  simp [xi_hypercube_weighted_spanning_tree_spectrum_product_treeWeight]

end Omega.Zeta
