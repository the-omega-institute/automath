import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part28b-strip-onset-law`. -/
theorem paper_xi_time_part28b_strip_onset_law {Scale : Type}
    (stripCertificate lowerEndpointOnset upperEndpointOnset negativeSideOnset : Scale → Prop)
    (hlower : ∀ L, stripCertificate L → lowerEndpointOnset L)
    (hupper : ∀ L, stripCertificate L → upperEndpointOnset L)
    (hneg : ∀ L, lowerEndpointOnset L → negativeSideOnset L) :
    ∀ L, stripCertificate L →
      And (lowerEndpointOnset L) (And (upperEndpointOnset L) (negativeSideOnset L)) := by
  intro L hstrip
  exact ⟨hlower L hstrip, hupper L hstrip, hneg L (hlower L hstrip)⟩

end Omega.Zeta
