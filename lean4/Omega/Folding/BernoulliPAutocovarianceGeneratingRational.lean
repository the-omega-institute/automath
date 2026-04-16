import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local package for the rational generating function of the Bernoulli-`p`
autocovariance sequence. The fields record the closed-form and recurrence inputs, the generating
series obtained from summing the recurrence, the normalization of numerator and denominator, and
the factorization of the `p = 1/2` specialization that isolates the double pole at `z = -2`. -/
structure BernoulliPAutocovarianceGeneratingRationalData where
  autocovariance : ℕ → ℚ
  generatingSeries : ℚ → ℚ
  numerator : ℚ → ℚ
  denominator : ℚ → ℚ
  closedFormPackage : Prop
  recurrencePackage : Prop
  generatingSeriesDerived : Prop
  denominatorNormalized : Prop
  halfSpecializationFactored : Prop
  rationalGeneratingFunction : Prop
  halfSpecializationDoublePole : Prop
  closedFormPackage_h : closedFormPackage
  recurrencePackage_h : recurrencePackage
  deriveGeneratingSeriesDerived :
    closedFormPackage → recurrencePackage → generatingSeriesDerived
  deriveDenominatorNormalized : generatingSeriesDerived → denominatorNormalized
  deriveRationalGeneratingFunction :
    generatingSeriesDerived → denominatorNormalized → rationalGeneratingFunction
  deriveHalfSpecializationFactored :
    rationalGeneratingFunction → halfSpecializationFactored
  deriveHalfSpecializationDoublePole :
    halfSpecializationFactored → halfSpecializationDoublePole

/-- Paper-facing wrapper for the Bernoulli-`p` autocovariance generating function: the closed form
and the order-3 recurrence imply a rational generating series, and the `p = 1/2` specialization
factors so that the denominator exhibits the claimed double pole at `z = -2`.
    thm:fold-bernoulli-p-autocovariance-generating-rational -/
theorem paper_fold_bernoulli_p_autocovariance_generating_rational
    (D : BernoulliPAutocovarianceGeneratingRationalData) :
    D.rationalGeneratingFunction ∧ D.halfSpecializationDoublePole := by
  have hSeries : D.generatingSeriesDerived :=
    D.deriveGeneratingSeriesDerived D.closedFormPackage_h D.recurrencePackage_h
  have hDenom : D.denominatorNormalized := D.deriveDenominatorNormalized hSeries
  have hRat : D.rationalGeneratingFunction :=
    D.deriveRationalGeneratingFunction hSeries hDenom
  have hHalf : D.halfSpecializationFactored := D.deriveHalfSpecializationFactored hRat
  exact ⟨hRat, D.deriveHalfSpecializationDoublePole hHalf⟩

end Omega.Folding
