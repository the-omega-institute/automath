namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zd-window6-three-site-toda-molecule`. -/
theorem paper_xi_time_part9zd_window6_three_site_toda_molecule
    (tauClosedForms todaFlaschkaEquations initialHamiltonian spectrumInvariant : Prop)
    (hTau : tauClosedForms)
    (hToda : tauClosedForms → todaFlaschkaEquations)
    (hInitial : tauClosedForms → initialHamiltonian)
    (hSpec : tauClosedForms → spectrumInvariant) :
    tauClosedForms ∧ todaFlaschkaEquations ∧ initialHamiltonian ∧ spectrumInvariant := by
  exact ⟨hTau, hToda hTau, hInitial hTau, hSpec hTau⟩

end Omega.Zeta
