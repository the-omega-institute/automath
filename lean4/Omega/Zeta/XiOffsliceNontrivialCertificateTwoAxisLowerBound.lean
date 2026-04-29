import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-offslice-nontrivial-certificate-two-axis-lower-bound`. -/
theorem paper_xi_offslice_nontrivial_certificate_two_axis_lower_bound
    (NeedsRadial NeedsPrime NoSingleAxis : Prop)
    (hRadial : NeedsRadial)
    (hPrime : NeedsPrime)
    (hOrthogonal : NeedsRadial → NeedsPrime → NoSingleAxis) :
    NeedsRadial ∧ NeedsPrime ∧ NoSingleAxis := by
  exact ⟨hRadial, hPrime, hOrthogonal hRadial hPrime⟩

end Omega.Zeta
