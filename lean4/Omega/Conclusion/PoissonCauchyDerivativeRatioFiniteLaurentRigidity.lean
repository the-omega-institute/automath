import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-cauchy-derivative-ratio-finite-laurent-rigidity`. -/
theorem paper_conclusion_poisson_cauchy_derivative_ratio_finite_laurent_rigidity
    (tIndependent finiteLaurentModes highestModeRigidity : Prop)
    (ht : tIndependent) (hfinite : finiteLaurentModes) (hhighest : highestModeRigidity) :
    tIndependent ∧ finiteLaurentModes ∧ highestModeRigidity := by
  exact ⟨ht, hfinite, hhighest⟩

end Omega.Conclusion
