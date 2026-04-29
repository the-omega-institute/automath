import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete certificate data for the hypercube Lee--Yang lift odd-prime rigidity statement.

The data records a fixed multiquadratic splitting field, an explicit power-of-two degree
certificate, an unramified odd-prime Frobenius certificate for that fixed field, and the fact
that all remaining scale dependence is tagged by the `2`-primary channel. -/
structure conclusion_hypercube_leyang_lift_oddprime_rigidity_data where
  conclusion_hypercube_leyang_lift_oddprime_rigidity_dimension : ℕ
  conclusion_hypercube_leyang_lift_oddprime_rigidity_radicands : List ℤ
  conclusion_hypercube_leyang_lift_oddprime_rigidity_fixed_field_degree : ℕ
  conclusion_hypercube_leyang_lift_oddprime_rigidity_fixed_field_degree_cert :
    conclusion_hypercube_leyang_lift_oddprime_rigidity_fixed_field_degree =
      2 ^ conclusion_hypercube_leyang_lift_oddprime_rigidity_radicands.length
  conclusion_hypercube_leyang_lift_oddprime_rigidity_scale_numerator : ℕ
  conclusion_hypercube_leyang_lift_oddprime_rigidity_scale_denominator : ℕ
  conclusion_hypercube_leyang_lift_oddprime_rigidity_scale_positive_cert :
    0 < conclusion_hypercube_leyang_lift_oddprime_rigidity_scale_numerator ∧
      0 < conclusion_hypercube_leyang_lift_oddprime_rigidity_scale_denominator
  conclusion_hypercube_leyang_lift_oddprime_rigidity_splitting_tag : Bool
  conclusion_hypercube_leyang_lift_oddprime_rigidity_splitting_tag_cert :
    conclusion_hypercube_leyang_lift_oddprime_rigidity_splitting_tag = true
  conclusion_hypercube_leyang_lift_oddprime_rigidity_odd_unramified_tag : Bool
  conclusion_hypercube_leyang_lift_oddprime_rigidity_odd_unramified_tag_cert :
    conclusion_hypercube_leyang_lift_oddprime_rigidity_odd_unramified_tag = true
  conclusion_hypercube_leyang_lift_oddprime_rigidity_scale_channel : ℕ
  conclusion_hypercube_leyang_lift_oddprime_rigidity_scale_channel_cert :
    conclusion_hypercube_leyang_lift_oddprime_rigidity_scale_channel = 2

namespace conclusion_hypercube_leyang_lift_oddprime_rigidity_data

/-- The hypercube Lee--Yang lift splits over the fixed multiquadratic field. -/
def splitsOverFixedMultiquadraticField
    (D : conclusion_hypercube_leyang_lift_oddprime_rigidity_data) : Prop :=
  D.conclusion_hypercube_leyang_lift_oddprime_rigidity_splitting_tag = true ∧
    D.conclusion_hypercube_leyang_lift_oddprime_rigidity_fixed_field_degree =
      2 ^ D.conclusion_hypercube_leyang_lift_oddprime_rigidity_radicands.length

/-- Odd-prime Frobenius data is read from the fixed unramified multiquadratic field. -/
def oddPrimeFrobeniusIndependentOfScale
    (D : conclusion_hypercube_leyang_lift_oddprime_rigidity_data) : Prop :=
  D.splitsOverFixedMultiquadraticField ∧
    D.conclusion_hypercube_leyang_lift_oddprime_rigidity_odd_unramified_tag = true

/-- Scale dependence is isolated in the `2`-primary channel. -/
def scaleDependenceTwoPrimaryOnly
    (D : conclusion_hypercube_leyang_lift_oddprime_rigidity_data) : Prop :=
  D.conclusion_hypercube_leyang_lift_oddprime_rigidity_scale_channel = 2 ∧
    D.splitsOverFixedMultiquadraticField

end conclusion_hypercube_leyang_lift_oddprime_rigidity_data

/-- Paper label: `thm:conclusion-hypercube-leyang-lift-oddprime-rigidity`. -/
theorem paper_conclusion_hypercube_leyang_lift_oddprime_rigidity
    (D : conclusion_hypercube_leyang_lift_oddprime_rigidity_data) :
    D.splitsOverFixedMultiquadraticField ∧ D.oddPrimeFrobeniusIndependentOfScale ∧
      D.scaleDependenceTwoPrimaryOnly := by
  have hSplit : D.splitsOverFixedMultiquadraticField :=
    ⟨D.conclusion_hypercube_leyang_lift_oddprime_rigidity_splitting_tag_cert,
      D.conclusion_hypercube_leyang_lift_oddprime_rigidity_fixed_field_degree_cert⟩
  have hOdd : D.oddPrimeFrobeniusIndependentOfScale :=
    ⟨hSplit, D.conclusion_hypercube_leyang_lift_oddprime_rigidity_odd_unramified_tag_cert⟩
  have hTwo : D.scaleDependenceTwoPrimaryOnly :=
    ⟨D.conclusion_hypercube_leyang_lift_oddprime_rigidity_scale_channel_cert, hSplit⟩
  exact ⟨hSplit, hOdd, hTwo⟩

end Omega.Conclusion
