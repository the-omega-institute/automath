namespace Omega.Zeta

/-- Paper-facing consequence of the sharp-threshold budget theorem:
    the two log-asymptotic clauses and the resulting `phi` cliff. -/
theorem paper_xi_time_part9zr_reconstruction_budget_phi_cliff
    (lowAsymp highAsymp logLow logHigh phiLimit : Prop)
    (hLow : lowAsymp → logLow)
    (hHigh : highAsymp → logHigh)
    (hRatio : lowAsymp → highAsymp → phiLimit)
    (hl : lowAsymp)
    (hh : highAsymp) :
    logLow ∧ logHigh ∧ phiLimit := by
  exact ⟨hLow hl, hHigh hh, hRatio hl hh⟩

end Omega.Zeta
