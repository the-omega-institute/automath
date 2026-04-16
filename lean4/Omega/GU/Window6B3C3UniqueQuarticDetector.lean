import Omega.GU.Window6B3C3QuarticRankoneHarmonicDetector

namespace Omega.GU

/-- Paper-facing corollary: both visible quartic defects vanish exactly on the radial quartic
subspace, i.e. when the unique `H₄` coefficient is zero.
    cor:window6-b3c3-unique-quartic-detector -/
theorem paper_window6_b3c3_unique_quartic_detector :
    ∀ q : QuarticInvariant, (b3QuarticError q = 0 ∧ c3QuarticError q = 0) ↔ q.2 = 0 := by
  intro q
  rcases paper_window6_b3c3_quartic_rankone_harmonic_detector with
    ⟨_, _, _, _, _, _, _, hb, hc⟩
  constructor
  · intro hq
    exact (hb q).1 hq.1
  · intro hq
    exact ⟨(hb q).2 hq, (hc q).2 hq⟩

end Omega.GU
