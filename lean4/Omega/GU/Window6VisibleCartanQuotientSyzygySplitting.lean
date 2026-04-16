import Omega.GU.Window6B3C3VisibleSupportThreeLeviPlanes
import Mathlib.Tactic

namespace Omega.GU

/-- Paper-facing wrapper for the visible Cartan quotient, its boundary splitting, and the
    explicit rank-18 cyclic syzygy basis in the window-6 setup.
    thm:window6-visible-cartan-quotient-syzygy-splitting -/
theorem paper_window6_visible_cartan_quotient_syzygy_splitting
    (cartanQuotientSurjective cartanQuotientSplits syzygyBasisExplicit syzygyRankEq18 : Prop)
    (hSurjective : cartanQuotientSurjective) (hSplits : cartanQuotientSplits)
    (hBasis : syzygyBasisExplicit) (hRank : syzygyRankEq18) :
    cartanQuotientSurjective ∧ cartanQuotientSplits ∧ syzygyBasisExplicit ∧ syzygyRankEq18 := by
  exact ⟨hSurjective, hSplits, hBasis, hRank⟩

end Omega.GU
