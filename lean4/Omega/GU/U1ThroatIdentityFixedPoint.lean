import Omega.GU.U1ThroatIdentity

namespace Omega.GU

/-- Paper-facing fixed-point wrapper for the unification-point identity.
    prop:u1-throat-identity -/
theorem paper_u1_throat_identity_fixed_point_seeds {u : ℝ} (hu : 0 < u) :
    u = 1 / u ↔ u = 1 :=
  Omega.GU.U1ThroatIdentity.paper_gut_u1_throat_identity_seeds hu

/-- Paper-facing theorem for `prop:u1-throat-identity`. -/
theorem paper_u1_throat_identity {u : ℝ} (hu : 0 < u) : u = 1 / u ↔ u = 1 := by
  exact Omega.GU.U1ThroatIdentity.paper_gut_u1_throat_identity_seeds hu

end Omega.GU
