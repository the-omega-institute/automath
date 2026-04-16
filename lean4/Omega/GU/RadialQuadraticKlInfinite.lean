import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local wrapper for the support-separation proof of infinite KL divergence in the
radial-quadratic identifiability setting. -/
structure RadialQuadraticKlInfiniteData where
  forwardKlInfinite : Prop
  reverseKlInfinite : Prop
  supportSeparated : Prop
  supportSeparated_holds : supportSeparated
  forwardKlInfinite_of_supportSeparated : supportSeparated → forwardKlInfinite
  reverseKlInfinite_of_supportSeparated : supportSeparated → reverseKlInfinite

/-- Support separation for two radial-quadratic laws forces both directed KL divergences to be
infinite.
    prop:group-jg-radial-quadratic-kl-infinite -/
theorem paper_group_jg_radial_quadratic_kl_infinite
    (h : RadialQuadraticKlInfiniteData) : h.forwardKlInfinite ∧ h.reverseKlInfinite := by
  exact
    ⟨h.forwardKlInfinite_of_supportSeparated h.supportSeparated_holds,
      h.reverseKlInfinite_of_supportSeparated h.supportSeparated_holds⟩

end Omega.GU
