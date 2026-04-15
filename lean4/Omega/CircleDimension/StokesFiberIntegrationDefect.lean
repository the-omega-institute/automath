import Mathlib.Tactic

namespace Omega.CircleDimension

section FiberIntegrationDefect

variable {RelForm BaseForm BoundaryForm : Type*} [AddCommGroup BaseForm]

/-- The Stokes defect after subtracting the signed fiberwise main term from the exterior
    derivative of the pushforward. -/
def fiberIntegrationDefect (dBase : BaseForm → BaseForm) (fiberPushforward : RelForm → BaseForm)
    (signedFiberDifferential : RelForm → BaseForm) (ω : RelForm) : BaseForm :=
  dBase (fiberPushforward ω) - signedFiberDifferential ω

/-- Minimal interface for the relative fiberwise Stokes formula with horizontal boundary vanishing
    and the remaining contribution localized on the vertical boundary. -/
def RelativeFiberStokes (horizontalBoundaryVanishing : Prop) (dBase : BaseForm → BaseForm)
    (fiberPushforward : RelForm → BaseForm) (signedFiberDifferential : RelForm → BaseForm)
    (verticalBoundaryRestrict : RelForm → BoundaryForm)
    (verticalBoundaryPushforward : BoundaryForm → BaseForm) : Prop :=
  horizontalBoundaryVanishing ∧
    ∀ ω, dBase (fiberPushforward ω) =
      signedFiberDifferential ω + verticalBoundaryPushforward (verticalBoundaryRestrict ω)

set_option maxHeartbeats 400000 in
/-- Paper-facing Stokes defect package: relativity removes the horizontal boundary, so the
    discrepancy between `d (π_! ω)` and the signed pushforward of `dω` is exactly the vertical
    boundary pushforward.
    prop:cdim-stokes-fiber-integration-defect -/
theorem paper_cdim_stokes_fiber_integration_defect
    (horizontalBoundaryVanishing : Prop) (dBase : BaseForm → BaseForm)
    (fiberPushforward : RelForm → BaseForm) (signedFiberDifferential : RelForm → BaseForm)
    (verticalBoundaryRestrict : RelForm → BoundaryForm)
    (verticalBoundaryPushforward : BoundaryForm → BaseForm)
    (hRel : horizontalBoundaryVanishing)
    (hStokes : ∀ ω, dBase (fiberPushforward ω) =
      signedFiberDifferential ω + verticalBoundaryPushforward (verticalBoundaryRestrict ω)) :
    RelativeFiberStokes horizontalBoundaryVanishing dBase fiberPushforward
        signedFiberDifferential verticalBoundaryRestrict verticalBoundaryPushforward ∧
      ∀ ω,
        fiberIntegrationDefect dBase fiberPushforward signedFiberDifferential ω =
          verticalBoundaryPushforward (verticalBoundaryRestrict ω) := by
  refine ⟨⟨hRel, hStokes⟩, ?_⟩
  intro ω
  unfold fiberIntegrationDefect
  rw [hStokes ω]
  abel

end FiberIntegrationDefect

end Omega.CircleDimension
