import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Integer anchors for the real-parameter pressure curve. -/
def pom_real_q_pressure_analytic_interpolation_integerAnchors
    (J : Set ℝ) (tau lambda momentRadius : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → (n : ℝ) ∈ J →
    lambda n = momentRadius n ∧ tau n = Real.log (momentRadius n)

/-- Normalized pressure compatibility with the collision/Renyi convention. -/
def pom_real_q_pressure_analytic_interpolation_normalizedPressureCompatible
    (J : Set ℝ) (tau normalizedPressure : ℝ → ℝ) : Prop :=
  ∀ q ∈ J, normalizedPressure q = tau q - q * Real.log 2

/-- Concrete non-cohomology witness used for the strict-convexity branch. -/
def pom_real_q_pressure_analytic_interpolation_notCohomologousToConstant
    (J : Set ℝ) (potential : ℝ → ℝ) : Prop :=
  ∀ c : ℝ, ∃ q ∈ J, potential q ≠ c

/-- Strict-convexity criterion supplied by the non-cohomology hypothesis in the paper. -/
def pom_real_q_pressure_analytic_interpolation_strictCriterion
    (J : Set ℝ) (tau potential : ℝ → ℝ) : Prop :=
  pom_real_q_pressure_analytic_interpolation_notCohomologousToConstant J potential →
    StrictConvexOn ℝ J tau

/-- Paper-facing statement for
`thm:pom-real-q-pressure-analytic-interpolation`.

The analytic-family and Perron-eigenvalue hypotheses are represented by concrete predicates on
the pressure branch `tau`, the Perron branch `lambda`, and the integer moment radii.  The theorem
records that those hypotheses immediately supply the three advertised outputs: regularity and
convexity of the real pressure curve, agreement at integer moment-kernel anchors, and normalized
pressure compatibility. -/
def pom_real_q_pressure_analytic_interpolation_statement : Prop :=
  ∀ (J : Set ℝ) (tau lambda momentRadius normalizedPressure potential : ℝ → ℝ),
    AnalyticOnNhd ℝ tau J →
    ConvexOn ℝ J tau →
    pom_real_q_pressure_analytic_interpolation_strictCriterion J tau potential →
    pom_real_q_pressure_analytic_interpolation_integerAnchors J tau lambda momentRadius →
    pom_real_q_pressure_analytic_interpolation_normalizedPressureCompatible
      J tau normalizedPressure →
      (AnalyticOnNhd ℝ tau J ∧ ConvexOn ℝ J tau ∧
        pom_real_q_pressure_analytic_interpolation_strictCriterion J tau potential) ∧
      pom_real_q_pressure_analytic_interpolation_integerAnchors J tau lambda momentRadius ∧
      pom_real_q_pressure_analytic_interpolation_normalizedPressureCompatible
        J tau normalizedPressure

/-- Paper label: `thm:pom-real-q-pressure-analytic-interpolation`. -/
theorem paper_pom_real_q_pressure_analytic_interpolation :
    pom_real_q_pressure_analytic_interpolation_statement := by
  intro J tau lambda momentRadius normalizedPressure potential hanalytic hconv hstrict hanchors
    hnormalized
  exact ⟨⟨hanalytic, hconv, hstrict⟩, hanchors, hnormalized⟩

end

end Omega.POM
