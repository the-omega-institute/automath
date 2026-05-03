import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-digital-local-factor-regularization-constraint`. The
regularized interpretation is the direct consequence of the rational local-factor obstruction
when rationality and infinitely many nonzero local operators both hold. -/
theorem paper_conclusion_digital_local_factor_regularization_constraint
    (localFactorRational infiniteNonzero needsRegularization : Prop)
    (hobstruction : localFactorRational -> infiniteNonzero -> needsRegularization)
    (hrat : localFactorRational) (hinf : infiniteNonzero) :
    needsRegularization := by
  exact hobstruction hrat hinf

end Omega.Conclusion
