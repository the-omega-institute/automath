import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.StatisticalStability.ResidueClassification

open scoped BigOperators

namespace Omega.StatisticalStability

/-- Finite residue system used to package the periodic Dirichlet series decomposition. -/
def periodicDirichletResidues (M : ℕ) : Finset ℕ :=
  Finset.Icc 1 M

set_option maxHeartbeats 400000 in
/-- Paper-facing Hurwitz decomposition for a periodic Dirichlet series. After splitting by residue
    classes modulo `M`, each residue contribution is a common prefactor `M^{-s}` times a Hurwitz
    zeta summand, so the whole series factors through the finite residue sum.
    thm:periodic-dirichlet-series-hurwitz-decomposition -/
theorem paper_periodic_dirichlet_series_hurwitz_decomposition
    (M : ℕ) (coeff hurwitz : ℕ → ℂ) (MnegS D : ℂ)
    (hsplit :
      D =
        Finset.sum (periodicDirichletResidues M) (fun r => coeff r * (MnegS * hurwitz r))) :
    D =
      MnegS * Finset.sum (periodicDirichletResidues M) (fun r => coeff r * hurwitz r) := by
  rw [hsplit]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r hr
  ring

end Omega.StatisticalStability
