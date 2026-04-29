import Omega.Zeta.XiComovingScanHankelRankDefect

namespace Omega.Zeta

/-- Paper label: `thm:xi-node-spectrum-minimal-window-2kappa`.
The `2κ` window recovers the finite atomic node spectrum by the full-rank
Hankel--Vandermonde certificate, while the supplied shorter-window ambiguity records the
irreducibility component. -/
theorem paper_xi_node_spectrum_minimal_window_2kappa (κ : Nat)
    (D : XiFiniteAtomicMomentData κ) (hweights : ∀ j : Fin κ, D.weights j ≠ 0)
    (hnodes : Function.Injective D.nodes) (shortWindowAmbiguous : Prop)
    (hshort : shortWindowAmbiguous) : D.hankel.rank = κ ∧ shortWindowAmbiguous := by
  exact ⟨(paper_xi_comoving_scan_hankel_rank_defect κ D hweights hnodes).2, hshort⟩

end Omega.Zeta
