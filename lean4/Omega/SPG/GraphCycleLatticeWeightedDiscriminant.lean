import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SPG

open scoped BigOperators

/-- Concrete finite data for the weighted cycle-lattice discriminant identity. Each complementary
minor factors as the full edge-weight product times the corresponding reciprocal tree monomial. -/
structure GraphCycleLatticeWeightedDiscriminantData where
  T : Type
  instDecidableEqT : DecidableEq T
  treeComplements : Finset T
  edgeWeightProduct : ℝ
  cycleMinor : T → ℝ
  reciprocalTreeWeight : T → ℝ
  minorFactorization : ∀ t, cycleMinor t = edgeWeightProduct * reciprocalTreeWeight t

attribute [instance] GraphCycleLatticeWeightedDiscriminantData.instDecidableEqT

namespace GraphCycleLatticeWeightedDiscriminantData

/-- The Gram determinant written as the Cauchy-Binet sum over complementary minors. -/
noncomputable def gramDet (D : GraphCycleLatticeWeightedDiscriminantData) : ℝ :=
  Finset.sum D.treeComplements D.cycleMinor

/-- The reciprocal weighted spanning-tree polynomial. -/
noncomputable def reciprocalTreePolynomial (D : GraphCycleLatticeWeightedDiscriminantData) : ℝ :=
  Finset.sum D.treeComplements D.reciprocalTreeWeight

end GraphCycleLatticeWeightedDiscriminantData

open GraphCycleLatticeWeightedDiscriminantData

/-- Summing the Cauchy-Binet complementary minors and factoring out the full edge-weight product
rewrites the cycle-lattice Gram determinant as the weighted discriminant formula.
    thm:graph-cycle-lattice-weighted-discriminant -/
theorem paper_graph_cycle_lattice_weighted_discriminant
    (D : GraphCycleLatticeWeightedDiscriminantData) :
    D.gramDet = D.edgeWeightProduct * D.reciprocalTreePolynomial := by
  unfold GraphCycleLatticeWeightedDiscriminantData.gramDet
  unfold GraphCycleLatticeWeightedDiscriminantData.reciprocalTreePolynomial
  calc
    Finset.sum D.treeComplements D.cycleMinor
      = Finset.sum D.treeComplements (fun t => D.edgeWeightProduct * D.reciprocalTreeWeight t) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          simp [D.minorFactorization t]
    _ = D.edgeWeightProduct * Finset.sum D.treeComplements D.reciprocalTreeWeight := by
          rw [Finset.mul_sum]
    _ = D.edgeWeightProduct * D.reciprocalTreePolynomial := by
          rfl

end Omega.SPG
