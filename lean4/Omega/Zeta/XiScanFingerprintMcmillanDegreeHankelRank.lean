import Omega.Zeta.XiComovingScanHankelRankDefect

namespace Omega.Zeta

/-- Paper label: `cor:xi-scan-fingerprint-mcmillan-degree-hankel-rank`. -/
theorem paper_xi_scan_fingerprint_mcmillan_degree_hankel_rank
    (κ : Nat) (D : XiFiniteAtomicMomentData κ)
    (hweights : ∀ j : Fin κ, D.weights j ≠ 0) (hnodes : Function.Injective D.nodes) :
    D.hankelDetFactorsAsVandermondeSquare ∧ D.hankel.rank = κ := by
  exact paper_xi_comoving_scan_hankel_rank_defect κ D hweights hnodes

end Omega.Zeta
