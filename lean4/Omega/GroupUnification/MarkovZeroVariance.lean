namespace Omega.GroupUnification

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the zero-variance criterion for finite-state
    Markov additive functionals in
    `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    lem:markov-zero-variance -/
theorem paper_zero_jitter_markov_zero_variance
    (poissonEquationSolution martingaleDecomposition asymptoticVarianceFormula
      zeroVarianceCriterion coboundaryRepresentation : Prop)
    (hDecomp : poissonEquationSolution → martingaleDecomposition)
    (hVariance : martingaleDecomposition → asymptoticVarianceFormula)
    (hCriterion : asymptoticVarianceFormula → (zeroVarianceCriterion ↔ coboundaryRepresentation)) :
    poissonEquationSolution →
      martingaleDecomposition ∧
        asymptoticVarianceFormula ∧
        (zeroVarianceCriterion ↔ coboundaryRepresentation) := by
  intro hPoisson
  have hDecomposition : martingaleDecomposition := hDecomp hPoisson
  have hAsymptotic : asymptoticVarianceFormula := hVariance hDecomposition
  exact ⟨hDecomposition, hAsymptotic, hCriterion hAsymptotic⟩

end Omega.GroupUnification
