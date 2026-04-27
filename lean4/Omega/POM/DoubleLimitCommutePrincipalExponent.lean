import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.POM.DoubleLimit

namespace Omega.POM

noncomputable section

/-- The principal endpoint exponent `(1 / 2) log φ`. -/
def pom_double_limit_commute_principal_exponent_principal_exponent : ℝ :=
  (1 / 2 : ℝ) * Real.log Real.goldenRatio

/-- Concrete endpoint-limit law for the two iterated routes. -/
abbrev pom_double_limit_commute_principal_exponent_law : Prop :=
  ∀ (qThenM mThenQ rqEndpoint maxEndpoint : ℝ),
    rqEndpoint = pom_double_limit_commute_principal_exponent_principal_exponent →
      maxEndpoint = pom_double_limit_commute_principal_exponent_principal_exponent →
        qThenM = rqEndpoint →
          mThenQ = maxEndpoint →
            qThenM = mThenQ ∧
              qThenM = pom_double_limit_commute_principal_exponent_principal_exponent ∧
              mThenQ = pom_double_limit_commute_principal_exponent_principal_exponent

/-- Paper label: `cor:pom-double-limit-commute-principal-exponent`. -/
theorem paper_pom_double_limit_commute_principal_exponent :
    pom_double_limit_commute_principal_exponent_law := by
  intro qThenM mThenQ rqEndpoint maxEndpoint hrq hmax hq hm
  exact paper_projection_double_limit qThenM mThenQ
    pom_double_limit_commute_principal_exponent_principal_exponent (hq.trans hrq)
    (hm.trans hmax)

end

end Omega.POM
