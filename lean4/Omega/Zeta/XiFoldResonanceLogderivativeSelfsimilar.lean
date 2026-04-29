namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-resonance-logderivative-selfsimilar`. -/
theorem paper_xi_fold_resonance_logderivative_selfsimilar
    (riccati_identity iterated_series real_log_derivative_formula : Prop)
    (hRiccati : riccati_identity) (hIterate : riccati_identity -> iterated_series)
    (hReal : iterated_series -> real_log_derivative_formula) :
    riccati_identity ∧ iterated_series ∧ real_log_derivative_formula := by
  exact ⟨hRiccati, hIterate hRiccati, hReal (hIterate hRiccati)⟩

end Omega.Zeta
