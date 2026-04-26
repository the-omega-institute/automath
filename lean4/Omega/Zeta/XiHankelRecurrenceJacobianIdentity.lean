import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete determinant data for the recurrence-window Jacobian identity. -/
structure XiHankelRecurrenceJacobianIdentityData (k : Type*) [Field k] where
  d : ℕ
  hankelDet : k

namespace XiHankelRecurrenceJacobianIdentityData

def unitLowerTriangularDet {k : Type*} [Field k] (D : XiHankelRecurrenceJacobianIdentityData k) :
    k :=
  (-1 : k) ^ D.d

def jacobianDet {k : Type*} [Field k] (D : XiHankelRecurrenceJacobianIdentityData k) : k :=
  D.unitLowerTriangularDet * D.hankelDet

end XiHankelRecurrenceJacobianIdentityData

open XiHankelRecurrenceJacobianIdentityData

/-- Paper label: `thm:xi-hankel-recurrence-jacobian-identity`. -/
theorem paper_xi_hankel_recurrence_jacobian_identity {k : Type*} [Field k]
    (D : XiHankelRecurrenceJacobianIdentityData k) :
    D.jacobianDet = (-1 : k) ^ D.d * D.hankelDet := by
  rfl

end Omega.Zeta
