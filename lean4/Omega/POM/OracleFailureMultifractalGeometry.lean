import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic
import Omega.POM.OracleFailureExponentDualityFromDoubleLdp
import Omega.POM.OracleIwIuAffineTilt

namespace Omega.POM

noncomputable section

/-- Concrete multifractal geometry package for the quadratic oracle-failure model. The microstate
spectrum `g` is the complement of the rate branch `I_w`, the upper tail is attained at the
endpoint `β = α log 2`, and the same endpoint gives the failure exponent. -/
def pom_oracle_failure_multifractal_geometry_statement
    (α slope offset curvature : ℝ) : Prop :=
  let c := α * Real.log 2
  let g : ℝ → ℝ := fun β => offset - (β - slope) ^ 2 / (2 * curvature)
  let E :=
    pom_oracle_failure_exponent_duality_from_double_ldp_failureExponent
      α slope offset curvature
  (∀ β : ℝ,
      pom_oracle_failure_exponent_duality_from_double_ldp_rate slope offset curvature β =
        pom_oracle_iw_iu_affine_tilt_iu slope offset curvature β - β +
          (Real.log 2 - Real.log Real.goldenRatio)) ∧
    (∀ β : ℝ,
      pom_oracle_failure_exponent_duality_from_double_ldp_rate slope offset curvature β =
        Real.log 2 - g β) ∧
    IsGreatest {x : ℝ | ∃ β : ℝ, c ≤ β ∧ x = g β} (g c) ∧
    IsLeast
      {x : ℝ | ∃ β : ℝ, c ≤ β ∧
          x =
            pom_oracle_failure_exponent_duality_from_double_ldp_rate
              slope offset curvature β}
      E ∧
    E = Real.log 2 - g c

/-- Paper label: `thm:pom-oracle-failure-multifractal-geometry`. In the concrete quadratic
oracle-failure package, the tail rate branch is `I_w(β) = log 2 - g(β)`, the microstate spectrum
`g` attains its tail supremum at the endpoint `β = α log 2`, and the same endpoint realizes the
failure exponent. -/
theorem paper_pom_oracle_failure_multifractal_geometry
    (α slope offset curvature : ℝ)
    (hcurv : 0 < curvature)
    (hα : slope < α * Real.log 2) :
    pom_oracle_failure_multifractal_geometry_statement α slope offset curvature := by
  dsimp [pom_oracle_failure_multifractal_geometry_statement]
  let c := α * Real.log 2
  let g : ℝ → ℝ := fun β => offset - (β - slope) ^ 2 / (2 * curvature)
  let E :=
    pom_oracle_failure_exponent_duality_from_double_ldp_failureExponent
      α slope offset curvature
  have htail :=
    paper_pom_oracle_failure_exponent_duality_from_double_ldp α slope offset curvature hcurv hα
  have htail_le :
      ∀ β : ℝ, c ≤ β →
        E ≤ pom_oracle_failure_exponent_duality_from_double_ldp_rate
          slope offset curvature β := by
    simpa [c, E] using htail.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro β
    simpa [pom_oracle_iw_iu_affine_tilt_iw] using
      paper_pom_oracle_iw_iu_affine_tilt β slope offset curvature
  · intro β
    change
      pom_oracle_failure_exponent_duality_from_double_ldp_rate slope offset curvature β =
        Real.log 2 - (offset - (β - slope) ^ 2 / (2 * curvature))
    unfold pom_oracle_failure_exponent_duality_from_double_ldp_rate
    ring
  · refine ⟨?_, ?_⟩
    · exact ⟨c, le_rfl, rfl⟩
    · intro x hx
      rcases hx with ⟨β, hβ, rfl⟩
      have hc_nonneg : 0 ≤ c - slope := by
        dsimp [c]
        linarith
      have hβ_nonneg : 0 ≤ β - slope := by
        linarith
      have hsq :
          (c - slope) ^ 2 ≤ (β - slope) ^ 2 := by
        nlinarith
      have hdenom : 0 < 2 * curvature := by positivity
      have hdiv :
          (c - slope) ^ 2 / (2 * curvature) ≤ (β - slope) ^ 2 / (2 * curvature) := by
        exact div_le_div_of_nonneg_right hsq (le_of_lt hdenom)
      change offset - (β - slope) ^ 2 / (2 * curvature) ≤
        offset - (c - slope) ^ 2 / (2 * curvature)
      linarith
  · refine ⟨?_, ?_⟩
    · refine ⟨c, le_rfl, ?_⟩
      simp [E, c, pom_oracle_failure_exponent_duality_from_double_ldp_failureExponent,
        pom_oracle_failure_exponent_duality_from_double_ldp_rate]
    · intro x hx
      rcases hx with ⟨β, hβ, rfl⟩
      exact htail_le β hβ
  · dsimp [E, g, c]
    unfold pom_oracle_failure_exponent_duality_from_double_ldp_failureExponent
      pom_oracle_failure_exponent_duality_from_double_ldp_rate
    ring

end

end Omega.POM
