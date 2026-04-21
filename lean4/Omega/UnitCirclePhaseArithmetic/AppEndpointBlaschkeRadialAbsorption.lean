import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The endpoint `-1` Poisson contribution of a single root. -/
def endpointPoissonMinusOne (a : ℂ) : ℝ :=
  (1 - ‖a‖ ^ 2) / ‖1 + a‖ ^ 2

/-- The first-order coefficient in the single-factor endpoint log-modulus expansion. -/
def singleBlaschkeEndpointLinearTerm (a : ℂ) : ℝ :=
  -endpointPoissonMinusOne a

/-- The endpoint absorption coefficient of a finite Blaschke product recorded by its root list. -/
def endpointBlaschkeRadialAbsorption (roots : List ℂ) : ℝ :=
  (roots.map endpointPoissonMinusOne).sum

/-- The summed first-order coefficient in the endpoint log-modulus expansion. -/
def endpointBlaschkeLogModulusLinearTerm (roots : List ℂ) : ℝ :=
  (roots.map singleBlaschkeEndpointLinearTerm).sum

/-- Concrete package for the endpoint `-1` radial absorption law of a finite Blaschke product. -/
def AppEndpointBlaschkeRadialAbsorptionStatement (roots : List ℂ) : Prop :=
  endpointBlaschkeLogModulusLinearTerm roots = -endpointBlaschkeRadialAbsorption roots ∧
    endpointBlaschkeRadialAbsorption roots = (roots.map endpointPoissonMinusOne).sum ∧
    (∀ a ∈ roots, ‖a‖ < 1 → 0 ≤ endpointPoissonMinusOne a) ∧
    ((∀ a ∈ roots, ‖a‖ < 1) → 0 ≤ endpointBlaschkeRadialAbsorption roots)

private lemma endpointPoissonMinusOne_nonneg {a : ℂ} (ha : ‖a‖ < 1) :
    0 ≤ endpointPoissonMinusOne a := by
  unfold endpointPoissonMinusOne
  have hnum : 0 ≤ 1 - ‖a‖ ^ 2 := by
    have hnorm_nonneg : 0 ≤ ‖a‖ := norm_nonneg _
    nlinarith
  have hden : 0 ≤ ‖1 + a‖ ^ 2 := by positivity
  exact div_nonneg hnum hden

private lemma endpointBlaschkeRadialAbsorption_nonneg {roots : List ℂ}
    (hroots : ∀ a ∈ roots, ‖a‖ < 1) : 0 ≤ endpointBlaschkeRadialAbsorption roots := by
  unfold endpointBlaschkeRadialAbsorption
  induction roots with
  | nil =>
      simp
  | cons a roots ih =>
      have ha : ‖a‖ < 1 := hroots a (by simp)
      have hrest : ∀ b ∈ roots, ‖b‖ < 1 := by
        intro b hb
        exact hroots b (by simp [hb])
      simpa using add_nonneg (endpointPoissonMinusOne_nonneg ha) (ih hrest)

/-- Paper label: `prop:app-endpoint-blaschke-radial-absorption`.
The summed single-factor endpoint coefficients assemble into the endpoint absorption sum, and the
absorption coefficient is nonnegative for roots lying in the open unit disk. -/
theorem paper_app_endpoint_blaschke_radial_absorption (roots : List ℂ) :
    AppEndpointBlaschkeRadialAbsorptionStatement roots := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · induction roots with
    | nil =>
        simp [endpointBlaschkeLogModulusLinearTerm, endpointBlaschkeRadialAbsorption]
    | cons a roots ih =>
        calc
          endpointBlaschkeLogModulusLinearTerm (a :: roots)
              = -endpointPoissonMinusOne a + endpointBlaschkeLogModulusLinearTerm roots := by
                  simp [endpointBlaschkeLogModulusLinearTerm, singleBlaschkeEndpointLinearTerm]
          _ = -endpointPoissonMinusOne a + -endpointBlaschkeRadialAbsorption roots := by
                rw [ih]
          _ = -(endpointPoissonMinusOne a + endpointBlaschkeRadialAbsorption roots) := by ring
          _ = -endpointBlaschkeRadialAbsorption (a :: roots) := by
                simp [endpointBlaschkeRadialAbsorption]
  · intro a ha hunit
    exact endpointPoissonMinusOne_nonneg hunit
  · intro hroots
    exact endpointBlaschkeRadialAbsorption_nonneg hroots

end

end Omega.UnitCirclePhaseArithmetic
