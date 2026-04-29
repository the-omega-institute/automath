namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zb-holonomic-bifurcation-fold-vs-resonance`. -/
theorem paper_xi_time_part9zb_holonomic_bifurcation_fold_vs_resonance
    (foldDfinite foldOrderTwo resonanceDfinite resonanceInfinitePoles resonancePRecursive : Prop)
    (hfold : foldDfinite)
    (horder : foldOrderTwo)
    (hfinite : resonanceDfinite → ¬ resonanceInfinitePoles)
    (hpoles : resonanceInfinitePoles)
    (hprec : resonancePRecursive → resonanceDfinite) :
    foldDfinite ∧ foldOrderTwo ∧ ¬ resonanceDfinite ∧ ¬ resonancePRecursive := by
  refine ⟨hfold, horder, ?_, ?_⟩
  · intro hres
    exact hfinite hres hpoles
  · intro hprecursive
    exact hfinite (hprec hprecursive) hpoles

end Omega.Zeta
