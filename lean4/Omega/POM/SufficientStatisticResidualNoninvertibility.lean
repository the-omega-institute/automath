import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local package for the sufficient-statistic residual noninvertibility criterion. The
paper argument bounds the residual image on each fiber by the rewrite-count degree plus one, then
rewrites the fiber multiplicity and degree in the closed forms tracked by these fields. -/
structure PomSufficientStatisticResidualData where
  imageCardLeDegreeSucc : Prop
  notFiberwiseInjectiveWhenMultiplicityExceedsDegreeSucc : Prop
  fiberFactorizationClosedForms : Prop
  imageCardLeDegreeSucc_h : imageCardLeDegreeSucc
  notFiberwiseInjectiveWhenMultiplicityExceedsDegreeSucc_h :
    notFiberwiseInjectiveWhenMultiplicityExceedsDegreeSucc
  fiberFactorizationClosedForms_h : fiberFactorizationClosedForms

/-- Paper-facing wrapper for the sufficient-statistic residual noninvertibility package.
    prop:pom-sufficient-statistic-residual-noninvertibility -/
theorem paper_pom_sufficient_statistic_residual_noninvertibility
    (h : PomSufficientStatisticResidualData) :
    h.imageCardLeDegreeSucc ∧ h.notFiberwiseInjectiveWhenMultiplicityExceedsDegreeSucc ∧
      h.fiberFactorizationClosedForms := by
  exact ⟨h.imageCardLeDegreeSucc_h, h.notFiberwiseInjectiveWhenMultiplicityExceedsDegreeSucc_h,
    h.fiberFactorizationClosedForms_h⟩

end Omega.POM
