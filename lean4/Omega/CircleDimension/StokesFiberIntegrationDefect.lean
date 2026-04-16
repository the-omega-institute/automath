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

set_option maxHeartbeats 400000 in
/-- The Stokes defect for a composite fiber integration splits into the pushed-forward main term,
the pushed-forward vertical boundary from the first stage, and the vertical boundary from the
second stage.
    thm:cdim-stokes-composite-fiber-integration-defect -/
theorem paper_cdim_stokes_composite_fiber_integration_defect
    {EForm BForm CForm EBoundary BBoundary : Type*} [AddCommGroup BForm] [AddCommGroup CForm]
    (dB : BForm -> BForm) (dC : CForm -> CForm) (piPush : EForm -> BForm)
    (sigmaPush : BForm -> CForm) (piMain : EForm -> BForm)
    (piBoundaryRestrict : EForm -> EBoundary) (piBoundaryPush : EBoundary -> BForm)
    (sigmaBoundaryRestrict : BForm -> BBoundary) (sigmaBoundaryPush : BBoundary -> CForm)
    (hSigmaAdd : forall x y, sigmaPush (x + y) = sigmaPush x + sigmaPush y)
    (hPi : forall omega, dB (piPush omega) =
      piMain omega + piBoundaryPush (piBoundaryRestrict omega))
    (hSigma : forall eta, dC (sigmaPush eta) =
      sigmaPush (dB eta) + sigmaBoundaryPush (sigmaBoundaryRestrict eta)) :
    forall omega,
      dC (sigmaPush (piPush omega)) =
        sigmaPush (piMain omega) +
          sigmaPush (piBoundaryPush (piBoundaryRestrict omega)) +
            sigmaBoundaryPush (sigmaBoundaryRestrict (piPush omega)) := by
  intro omega
  rw [hSigma, hPi, hSigmaAdd]

end FiberIntegrationDefect

end Omega.CircleDimension
