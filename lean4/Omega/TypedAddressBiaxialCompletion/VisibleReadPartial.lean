import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete chapter-local package for the visible-domain partial read rule. It records the state
space, the observation type, the guarded readout, and the advertised case split. -/
structure VisibleReadPartialData where
  State : Type
  Obs : Type
  read : State → Option Obs
  inDomain : State → Bool
  inVisiblePhase : State → Bool
  checkPasses : State → Bool
  obs : State → Obs
  guarded_read :
    ∀ ω, read ω = if inDomain ω && inVisiblePhase ω && checkPasses ω then some (obs ω) else none

/-- On the visible phase domain, the typed-address readout is exactly the advertised guarded
partial function: it returns the observed value precisely when the address is in-domain, visible,
and passes the checker, and returns `none` otherwise.
    prop:typed-address-biaxial-completion-visible-read-partial -/
theorem paper_typed_address_biaxial_completion_visible_read_partial (D : VisibleReadPartialData) :
    ∀ ω,
      D.read ω =
        if D.inDomain ω && D.inVisiblePhase ω && D.checkPasses ω then some (D.obs ω) else none := by
  exact D.guarded_read

end Omega.TypedAddressBiaxialCompletion
