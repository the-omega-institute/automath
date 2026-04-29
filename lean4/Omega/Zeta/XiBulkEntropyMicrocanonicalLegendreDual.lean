import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite-bulk data for the microcanonical Legendre dual formula. -/
structure xi_bulk_entropy_microcanonical_legendre_dual_Data where
  kappa : ℕ
  delta : Fin kappa → ℝ
  saddle : ℝ

namespace xi_bulk_entropy_microcanonical_legendre_dual_Data

/-- Logistic occupancy at coordinate `j` and natural parameter `s`. -/
def occupancy (D : xi_bulk_entropy_microcanonical_legendre_dual_Data) (s : ℝ)
    (j : Fin D.kappa) : ℝ :=
  Real.exp s * D.delta j / (1 + Real.exp s * D.delta j)

/-- The finite grand potential for the logistic occupancies. -/
def grandPotential (D : xi_bulk_entropy_microcanonical_legendre_dual_Data) (s : ℝ) : ℝ :=
  ∑ j : Fin D.kappa, Real.log (1 + Real.exp s * D.delta j)

/-- The total logistic mass at the saddle. -/
def totalOccupancy (D : xi_bulk_entropy_microcanonical_legendre_dual_Data) : ℝ :=
  ∑ j : Fin D.kappa, occupancy D D.saddle j

/-- Microcanonical entropy as the Legendre transform evaluated at the saddle. -/
def microcanonicalEntropy (D : xi_bulk_entropy_microcanonical_legendre_dual_Data) : ℝ :=
  grandPotential D D.saddle - D.saddle * totalOccupancy D

/-- The displayed coordinatewise entropy formula after substituting the logistic occupancies. -/
def binaryEntropySum (D : xi_bulk_entropy_microcanonical_legendre_dual_Data) : ℝ :=
  ∑ j : Fin D.kappa,
    (Real.log (1 + Real.exp D.saddle * D.delta j) -
      D.saddle * occupancy D D.saddle j)

/-- Paper-facing Legendre-dual identity. -/
def legendre_dual_formula (D : xi_bulk_entropy_microcanonical_legendre_dual_Data) : Prop :=
  microcanonicalEntropy D = binaryEntropySum D

end xi_bulk_entropy_microcanonical_legendre_dual_Data

/-- Paper label: `prop:xi-bulk-entropy-microcanonical-legendre-dual`. -/
theorem paper_xi_bulk_entropy_microcanonical_legendre_dual
    (D : xi_bulk_entropy_microcanonical_legendre_dual_Data) :
    D.legendre_dual_formula := by
  unfold xi_bulk_entropy_microcanonical_legendre_dual_Data.legendre_dual_formula
    xi_bulk_entropy_microcanonical_legendre_dual_Data.microcanonicalEntropy
    xi_bulk_entropy_microcanonical_legendre_dual_Data.binaryEntropySum
    xi_bulk_entropy_microcanonical_legendre_dual_Data.grandPotential
    xi_bulk_entropy_microcanonical_legendre_dual_Data.totalOccupancy
  rw [Finset.sum_sub_distrib]
  rw [Finset.mul_sum]

end

end Omega.Zeta
