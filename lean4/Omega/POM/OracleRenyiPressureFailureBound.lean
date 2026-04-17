import Omega.Folding.MomentSum

namespace Omega.POM

/-- Chapter-local package for the oracle Rényi-pressure failure estimate. The data record the
identification `S_q(m) = Omega.momentSum q m`, the pointwise `(u - t)_+` control, the normalized
rewriting that yields the finite-volume failure inequality, and the pressure input used to pass to
the limsup and error-exponent conclusions. -/
structure OracleRenyiPressureFailureBoundData where
  q : Nat
  Sq : Nat → Nat
  failureBound : Prop
  pressureLimsupBound : Prop
  errorExponentLowerBound : Prop
  q_gt_one : 1 < q
  Sq_eq_momentSum : Sq = Omega.momentSum q
  pointwisePositivePartBound : Prop
  normalizedQuantityRewrite : Prop
  pressureLimit : Prop
  pointwisePositivePartBound_h : pointwisePositivePartBound
  normalizedQuantityRewrite_h : normalizedQuantityRewrite
  pressureLimit_h : pressureLimit
  deriveFailureBound :
    Sq = Omega.momentSum q →
      pointwisePositivePartBound →
        normalizedQuantityRewrite → failureBound
  derivePressureLimsupBound :
    failureBound → pressureLimit → pressureLimsupBound
  deriveErrorExponentLowerBound :
    pressureLimsupBound → pressureLimit → errorExponentLowerBound

/-- Paper-facing wrapper for the oracle Rényi-pressure failure estimate: first derive the
finite-volume failure bound from the `momentSum` normalization and the pointwise bound, then use
the pressure input to package the limsup inequality and the resulting error-exponent lower bound.
    thm:pom-oracle-renyi-pressure-failure-bound -/
theorem paper_pom_oracle_renyi_pressure_failure_bound
    (D : OracleRenyiPressureFailureBoundData) :
    And D.failureBound (And D.pressureLimsupBound D.errorExponentLowerBound) := by
  have hFailure : D.failureBound :=
    D.deriveFailureBound D.Sq_eq_momentSum D.pointwisePositivePartBound_h
      D.normalizedQuantityRewrite_h
  have hLimsup : D.pressureLimsupBound :=
    D.derivePressureLimsupBound hFailure D.pressureLimit_h
  have hExponent : D.errorExponentLowerBound :=
    D.deriveErrorExponentLowerBound hLimsup D.pressureLimit_h
  exact ⟨hFailure, hLimsup, hExponent⟩

end Omega.POM
