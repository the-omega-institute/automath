import Mathlib.Tactic
import Omega.CircleDimension.CircleDim

namespace Omega.Conclusion

open Omega.CircleDimension

/-- Concrete bookkeeping package for a finite-rank torsion-free group with a chosen lattice inside
its `ℚ`-span. The lattice contributes the free rank `rankQ`, while the quotient contributes only a
finite torsion card. -/
structure conclusion_cdim_finite_rank_extension_data where
  rankQ : Nat
  quotientTorsionCard : Nat

namespace conclusion_cdim_finite_rank_extension_data

/-- The chosen lattice has the ambient `ℚ`-rank. -/
abbrev conclusion_cdim_finite_rank_extension_lattice_rank
    (D : conclusion_cdim_finite_rank_extension_data) : Nat :=
  D.rankQ

/-- The connected circle dimension is modeled by the free lattice together with the finite torsion
quotient; the latter is invisible to `circleDim`. -/
def connected_circle_dim (D : conclusion_cdim_finite_rank_extension_data) : Nat :=
  circleDim D.conclusion_cdim_finite_rank_extension_lattice_rank D.quotientTorsionCard

/-- Clearing denominators shows that the quotient by the chosen lattice contributes only finite
torsion data, so the circle dimension is unchanged after discarding it. -/
theorem conclusion_cdim_finite_rank_extension_quotient_torsion
    (D : conclusion_cdim_finite_rank_extension_data) :
    circleDim D.rankQ D.quotientTorsionCard = circleDim D.rankQ 0 :=
  circleDim_finite_extension D.rankQ D.quotientTorsionCard 0

/-- The identity component ignores the totally disconnected quotient. -/
theorem conclusion_cdim_finite_rank_extension_connected_component
    (D : conclusion_cdim_finite_rank_extension_data) :
    D.connected_circle_dim = circleDim D.rankQ 0 := by
  unfold connected_circle_dim
  simpa using D.conclusion_cdim_finite_rank_extension_quotient_torsion

end conclusion_cdim_finite_rank_extension_data

open conclusion_cdim_finite_rank_extension_data

/-- Paper label: `thm:conclusion-cdim-finite-rank-extension`. In the finite-rank bookkeeping
model, the totally disconnected torsion quotient does not affect the connected circle dimension, so
the latter agrees with the `ℚ`-rank. -/
theorem paper_conclusion_cdim_finite_rank_extension
    (D : conclusion_cdim_finite_rank_extension_data) : D.connected_circle_dim = D.rankQ := by
  calc
    D.connected_circle_dim = circleDim D.rankQ 0 :=
      D.conclusion_cdim_finite_rank_extension_connected_component
    _ = D.rankQ := by simp [circleDim]

end Omega.Conclusion
