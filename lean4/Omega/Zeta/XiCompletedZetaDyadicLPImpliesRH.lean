namespace Omega.Zeta

/-- Paper label: `thm:xi-completed-zeta-dyadic-lp-implies-rh`. -/
theorem paper_xi_completed_zeta_dyadic_lp_implies_rh
    (dyadicLPClosure compactUniformConvergence hurwitzZeroTransfer riemannHypothesis : Prop)
    (hHurwitz : dyadicLPClosure → compactUniformConvergence → hurwitzZeroTransfer)
    (hRH : hurwitzZeroTransfer → riemannHypothesis) (hLP : dyadicLPClosure)
    (hLimit : compactUniformConvergence) : riemannHypothesis := by
  exact hRH (hHurwitz hLP hLimit)

end Omega.Zeta
