import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete inverse-limit data for the cross-resolution affine rigidity statement. `projection`
reads the finite-level coordinates of a limit point, `projection_injective` says those coordinates
determine the limit point uniquely, and the two lifts agree after every finite projection. -/
structure XiCrossResolutionAffineRigidityData where
  Action : Type
  Point : Type
  finiteLevel : ℕ → Type
  projection : ∀ n, Point → finiteLevel n
  projection_injective : Function.Injective fun x n => projection n x
  canonicalLift : Action → Point → Point
  comparisonLift : Action → Point → Point
  finite_level_agree :
    ∀ h x n, projection n (comparisonLift h x) = projection n (canonicalLift h x)

namespace XiCrossResolutionAffineRigidityData

/-- The comparison lift is unique when every finite-level coordinate agrees with the canonical
inverse-limit lift. -/
def uniqueLift (D : XiCrossResolutionAffineRigidityData) : Prop :=
  D.comparisonLift = D.canonicalLift

end XiCrossResolutionAffineRigidityData

/-- Paper label: `thm:xi-time-part9g-cross-resolution-affine-rigidity`.
Agreement on every finite quotient forces the two inverse-limit lifts to coincide. -/
theorem paper_xi_time_part9g_cross_resolution_affine_rigidity
    (D : XiCrossResolutionAffineRigidityData) : D.uniqueLift := by
  unfold XiCrossResolutionAffineRigidityData.uniqueLift
  funext h x
  apply D.projection_injective
  funext n
  exact D.finite_level_agree h x n

end Omega.Zeta
