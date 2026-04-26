import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Quadratic pressure profile used for the concrete double-LDP duality surrogate. -/
def pom_oracle_failure_exponent_duality_from_double_ldp_tau
    (slope offset curvature q : ℝ) : ℝ :=
  offset + slope * (q - 1) + curvature / 2 * (q - 1) ^ 2

/-- Critical order solving `τ'(q) = α log 2`. -/
def pom_oracle_failure_exponent_duality_from_double_ldp_criticalOrder
    (α slope curvature : ℝ) : ℝ :=
  1 + (α * Real.log 2 - slope) / curvature

/-- Quadratic rate function coming from the Legendre transform of the pressure CGF. -/
def pom_oracle_failure_exponent_duality_from_double_ldp_rate
    (slope offset curvature β : ℝ) : ℝ :=
  Real.log 2 - offset + (β - slope) ^ 2 / (2 * curvature)

/-- Chernoff/Legendre objective at slope `α log 2`. -/
def pom_oracle_failure_exponent_duality_from_double_ldp_objective
    (α slope offset curvature q : ℝ) : ℝ :=
  Real.log 2 + (q - 1) * (α * Real.log 2) -
    pom_oracle_failure_exponent_duality_from_double_ldp_tau slope offset curvature q

/-- Closed failure exponent produced by the quadratic duality computation. -/
def pom_oracle_failure_exponent_duality_from_double_ldp_failureExponent
    (α slope offset curvature : ℝ) : ℝ :=
  pom_oracle_failure_exponent_duality_from_double_ldp_rate
    slope offset curvature (α * Real.log 2)

private lemma pom_oracle_failure_exponent_duality_from_double_ldp_objective_eq
    (α slope offset curvature q : ℝ) :
    pom_oracle_failure_exponent_duality_from_double_ldp_objective α slope offset curvature q =
      Real.log 2 - offset + (α * Real.log 2 - slope) * (q - 1) -
        curvature / 2 * (q - 1) ^ 2 := by
  unfold pom_oracle_failure_exponent_duality_from_double_ldp_objective
    pom_oracle_failure_exponent_duality_from_double_ldp_tau
  ring

private lemma pom_oracle_failure_exponent_duality_from_double_ldp_objective_completeSquare
    (α slope offset curvature q : ℝ) (hcurv : 0 < curvature) :
    pom_oracle_failure_exponent_duality_from_double_ldp_objective α slope offset curvature q =
      pom_oracle_failure_exponent_duality_from_double_ldp_failureExponent α slope offset curvature -
        curvature / 2 *
          (q -
            pom_oracle_failure_exponent_duality_from_double_ldp_criticalOrder
              α slope curvature) ^ 2 := by
  have hcurv_ne : curvature ≠ 0 := ne_of_gt hcurv
  unfold pom_oracle_failure_exponent_duality_from_double_ldp_failureExponent
    pom_oracle_failure_exponent_duality_from_double_ldp_rate
    pom_oracle_failure_exponent_duality_from_double_ldp_criticalOrder
  rw [pom_oracle_failure_exponent_duality_from_double_ldp_objective_eq]
  field_simp [hcurv_ne]
  ring

/-- Paper label: `thm:pom-oracle-failure-exponent-duality-from-double-ldp`.
In the concrete quadratic pressure model, the critical order is unique, the Chernoff objective
attains the exact failure exponent there, and the resulting exponent is the threshold-tail value
of the quadratic rate function. -/
theorem paper_pom_oracle_failure_exponent_duality_from_double_ldp
    (α slope offset curvature : ℝ)
    (hcurv : 0 < curvature)
    (hα : slope < α * Real.log 2) :
    let qStar :=
      pom_oracle_failure_exponent_duality_from_double_ldp_criticalOrder α slope curvature
    let E :=
      pom_oracle_failure_exponent_duality_from_double_ldp_failureExponent
        α slope offset curvature
    (∃! q : ℝ, 1 < q ∧ α * Real.log 2 = slope + curvature * (q - 1)) ∧
      pom_oracle_failure_exponent_duality_from_double_ldp_objective
          α slope offset curvature qStar = E ∧
      (∀ q : ℝ, 1 < q →
        pom_oracle_failure_exponent_duality_from_double_ldp_objective
          α slope offset curvature q ≤ E) ∧
      (∀ β : ℝ, α * Real.log 2 ≤ β →
        E ≤ pom_oracle_failure_exponent_duality_from_double_ldp_rate
          slope offset curvature β) ∧
      E =
        Real.log 2 - offset + (α * Real.log 2 - slope) ^ 2 / (2 * curvature) := by
  dsimp
  have hcurv_ne : curvature ≠ 0 := ne_of_gt hcurv
  have hdelta_pos : 0 < α * Real.log 2 - slope := by
    linarith
  have hqStar_gt :
      1 <
        pom_oracle_failure_exponent_duality_from_double_ldp_criticalOrder
          α slope curvature := by
    unfold pom_oracle_failure_exponent_duality_from_double_ldp_criticalOrder
    have hfrac_pos : 0 < (α * Real.log 2 - slope) / curvature := div_pos hdelta_pos hcurv
    linarith
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · refine
      ⟨pom_oracle_failure_exponent_duality_from_double_ldp_criticalOrder α slope curvature,
        ?_, ?_⟩
    · refine ⟨hqStar_gt, ?_⟩
      unfold pom_oracle_failure_exponent_duality_from_double_ldp_criticalOrder
      field_simp [hcurv_ne]
      ring
    · intro q hq
      rcases hq with ⟨_, hq_eq⟩
      have hlin : curvature * (q - 1) = α * Real.log 2 - slope := by
        linarith
      have hdiv : q - 1 = (α * Real.log 2 - slope) / curvature := by
        apply (eq_div_iff hcurv_ne).2
        simpa [mul_comm, mul_left_comm, mul_assoc] using hlin
      unfold pom_oracle_failure_exponent_duality_from_double_ldp_criticalOrder
      linarith
  · rw [pom_oracle_failure_exponent_duality_from_double_ldp_objective_completeSquare
      α slope offset curvature
      (pom_oracle_failure_exponent_duality_from_double_ldp_criticalOrder α slope curvature)
      hcurv]
    simp
  · intro q _
    rw [pom_oracle_failure_exponent_duality_from_double_ldp_objective_completeSquare
      α slope offset curvature q hcurv]
    have hnonneg :
        0 ≤ curvature / 2 *
          (q -
            pom_oracle_failure_exponent_duality_from_double_ldp_criticalOrder
              α slope curvature) ^ 2 := by
      positivity
    linarith
  · intro β hβ
    have hshift_nonneg : 0 ≤ α * Real.log 2 - slope := by
      linarith
    have hmono : α * Real.log 2 - slope ≤ β - slope := by
      linarith
    have hsquare :
        (α * Real.log 2 - slope) ^ 2 ≤ (β - slope) ^ 2 := by
      nlinarith
    unfold pom_oracle_failure_exponent_duality_from_double_ldp_failureExponent
      pom_oracle_failure_exponent_duality_from_double_ldp_rate
    have hdenom : 0 < 2 * curvature := by positivity
    have hdiv :
        (α * Real.log 2 - slope) ^ 2 / (2 * curvature) ≤ (β - slope) ^ 2 / (2 * curvature) := by
      exact div_le_div_of_nonneg_right hsquare (le_of_lt hdenom)
    linarith

end

end Omega.POM
