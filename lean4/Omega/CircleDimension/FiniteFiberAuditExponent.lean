import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Minimal bookkeeping model for the phase-audit exponent: finite fibers contribute only to the
    torsion register, so the exponent is governed by the circle dimension.
    prop:cdim-finite-fiber-does-not-change-audit-exponent -/
def auditExponent (freeRank finiteFiber : Nat) : Nat :=
  circleDim freeRank finiteFiber

/-- Restricting an audit scheme from `G ⊕ F` to `G` cannot decrease the exponent.
    prop:cdim-finite-fiber-does-not-change-audit-exponent -/
theorem auditExponent_restrict (freeRank torsion fiber : Nat) :
    auditExponent freeRank torsion ≤ auditExponent freeRank (torsion + fiber) := by
  simpa [auditExponent] using le_of_eq (circleDim_finite_extension freeRank torsion (torsion + fiber))

/-- Extending an audit scheme on `G` by recording the finite fiber in a constant-size register
    does not increase the exponent.
    prop:cdim-finite-fiber-does-not-change-audit-exponent -/
theorem auditExponent_extend (freeRank torsion fiber : Nat) :
    auditExponent freeRank (torsion + fiber) ≤ auditExponent freeRank torsion := by
  simpa [auditExponent] using le_of_eq (circleDim_finite_extension freeRank torsion (torsion + fiber)).symm

/-- Adding a finite fiber does not change the phase-audit exponent.
    prop:cdim-finite-fiber-does-not-change-audit-exponent -/
theorem paper_cdim_finite_fiber_does_not_change_audit_exponent
    (freeRank torsion fiber : Nat) :
    auditExponent freeRank (torsion + fiber) = auditExponent freeRank torsion := by
  exact le_antisymm
    (auditExponent_extend freeRank torsion fiber)
    (auditExponent_restrict freeRank torsion fiber)

end Omega.CircleDimension
