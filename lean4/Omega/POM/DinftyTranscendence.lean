import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Basic

namespace Omega.POM

noncomputable section

/-- The endpoint logarithmic ratio `log 2 / log φ` used in the audited `D_infty` exponent. -/
def pom_dinfty_transcendence_log_ratio : ℝ :=
  Real.log 2 / Real.log Real.goldenRatio

/-- The endpoint exponent `D_infty = log(2)/log(φ) - 1/2`. -/
def pom_dinfty_transcendence_endpoint_exponent : ℝ :=
  pom_dinfty_transcendence_log_ratio - (1 / 2 : ℝ)

/-- Concrete data isolating the two external number-theory inputs used by the paper proof:
irrationality of `log 2 / log φ`, and the transcendence transfer to `D_infty` and `2D_infty`. -/
structure pom_dinfty_transcendence_data where
  pom_dinfty_transcendence_ratio_irrational :
    Irrational pom_dinfty_transcendence_log_ratio
  pom_dinfty_transcendence_transcendence_step :
    Irrational pom_dinfty_transcendence_log_ratio →
      Transcendental ℚ pom_dinfty_transcendence_endpoint_exponent ∧
        Transcendental ℚ (2 * pom_dinfty_transcendence_endpoint_exponent)

namespace pom_dinfty_transcendence_data

/-- Paper-facing endpoint transcendence predicate. -/
def pom_dinfty_transcendence_is_transcendental
    (_D : pom_dinfty_transcendence_data) : Prop :=
  Transcendental ℚ pom_dinfty_transcendence_endpoint_exponent

/-- Paper-facing doubled endpoint transcendence predicate. -/
def pom_dinfty_transcendence_double_is_transcendental
    (_D : pom_dinfty_transcendence_data) : Prop :=
  Transcendental ℚ (2 * pom_dinfty_transcendence_endpoint_exponent)

end pom_dinfty_transcendence_data

/-- Paper label: `thm:pom-Dinfty-transcendence`. -/
theorem paper_pom_dinfty_transcendence (D : pom_dinfty_transcendence_data) :
    D.pom_dinfty_transcendence_is_transcendental ∧
      D.pom_dinfty_transcendence_double_is_transcendental := by
  exact D.pom_dinfty_transcendence_transcendence_step
    D.pom_dinfty_transcendence_ratio_irrational

end

end Omega.POM
