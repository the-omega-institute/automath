import Mathlib.Tactic

namespace Omega.Discussion

/-- Chapter-local wrapper for the fold-6 horizon-measure candidate. It records the finite
pushforward measure produced by the fold/phase data, the standard Carathéodory positivity step
for positive circle measures, the Toeplitz--PSD Gram-matrix consequence, and the optional
weak-limit observation used for the asymptotic audit discussion. -/
structure HorizonMeasureFold6PushforwardData where
  finiteFoldPushforwardMeasure : Prop
  finiteFoldPushforwardMeasure_h : finiteFoldPushforwardMeasure
  positiveCircleMeasure : Prop
  caratheodoryHerglotzPositivity : Prop
  toeplitzPsdHierarchy : Prop
  weakLimitExists : Prop
  weakLimitAuditInput : Prop
  packagePositiveCircleMeasure :
    finiteFoldPushforwardMeasure → positiveCircleMeasure
  deriveCaratheodoryHerglotzPositivity :
    positiveCircleMeasure → caratheodoryHerglotzPositivity
  deriveToeplitzPsdHierarchy :
    positiveCircleMeasure → caratheodoryHerglotzPositivity → toeplitzPsdHierarchy
  weakLimitFeedsAudit :
    weakLimitExists → weakLimitAuditInput

/-- Discussion-facing wrapper for the fold-6 horizon-measure pushforward proposition: the
fold-induced finite pushforward law packages a positive circle measure, standard
Carathéodory/Herglotz positivity yields nonnegative real part, the associated Toeplitz matrices
are Gram-positive, and any weak limit can be restated as an audit-input clause.
    prop:discussion-horizon-measure-fold6-pushforward -/
theorem paper_discussion_horizon_measure_fold6_pushforward
    (D : HorizonMeasureFold6PushforwardData) :
    D.positiveCircleMeasure ∧ D.caratheodoryHerglotzPositivity ∧ D.toeplitzPsdHierarchy ∧
      (D.weakLimitExists → D.weakLimitAuditInput) := by
  have hMeasure : D.positiveCircleMeasure :=
    D.packagePositiveCircleMeasure D.finiteFoldPushforwardMeasure_h
  have hPositive : D.caratheodoryHerglotzPositivity :=
    D.deriveCaratheodoryHerglotzPositivity hMeasure
  exact ⟨hMeasure, hPositive, D.deriveToeplitzPsdHierarchy hMeasure hPositive,
    D.weakLimitFeedsAudit⟩

end Omega.Discussion
