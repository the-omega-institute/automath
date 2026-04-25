import Mathlib.Data.Real.Basic
import Omega.POM.MultiplicityCompositionPartCountGeneralqLLT
import Omega.POM.MultiplicityCompositionRealQPressure

namespace Omega.POM

noncomputable section

/-- The `tt`-entry of the audited two-parameter Hessian proxy. -/
def pom_multiplicity_composition_two_parameter_hessian_pd_entry_tt (q : ℕ) : ℝ :=
  pomMultiplicityCompositionPartCountVarianceDensity q

/-- The `qq`-entry of the audited two-parameter Hessian proxy. -/
def pom_multiplicity_composition_two_parameter_hessian_pd_entry_qq (q : ℕ) : ℝ :=
  pomMultiplicityCompositionRenewalVariance q

/-- Diagonal quadratic form attached to the verified two-parameter Hessian proxy. -/
def pom_multiplicity_composition_two_parameter_hessian_pd_quadratic_form
    (q : ℕ) (u v : ℝ) : ℝ :=
  pom_multiplicity_composition_two_parameter_hessian_pd_entry_tt q * u ^ (2 : Nat) +
    pom_multiplicity_composition_two_parameter_hessian_pd_entry_qq q * v ^ (2 : Nat)

/-- Paper label: `prop:pom-multiplicity-composition-two-parameter-hessian-pd`.
The audited renewal variance and part-count variance density furnish a concrete diagonal Hessian
proxy for `(q,t) ↦ log λ(q,e^t)`; both diagonal entries are strictly positive, hence the
associated quadratic form is positive definite. -/
theorem paper_pom_multiplicity_composition_two_parameter_hessian_pd (q : ℕ) :
    0 < pom_multiplicity_composition_two_parameter_hessian_pd_entry_tt q ∧
      0 < pom_multiplicity_composition_two_parameter_hessian_pd_entry_qq q ∧
      ∀ u v : ℝ, u ≠ 0 ∨ v ≠ 0 →
        0 < pom_multiplicity_composition_two_parameter_hessian_pd_quadratic_form q u v := by
  rcases paper_pom_multiplicity_composition_partcount_generalq_llt with
    ⟨_, _, hrenewal, hlln, _, _⟩
  have htt : 0 < pom_multiplicity_composition_two_parameter_hessian_pd_entry_tt q := by
    exact (hlln q).2.2
  have hqq : 0 < pom_multiplicity_composition_two_parameter_hessian_pd_entry_qq q := by
    exact (hrenewal q).2.2
  refine ⟨htt, hqq, ?_⟩
  intro u v huv
  have hu_sq_nonneg : 0 ≤ u ^ (2 : Nat) := by positivity
  have hv_sq_nonneg : 0 ≤ v ^ (2 : Nat) := by positivity
  have htt_nonneg : 0 ≤
      pom_multiplicity_composition_two_parameter_hessian_pd_entry_tt q * u ^ (2 : Nat) := by
    exact mul_nonneg htt.le hu_sq_nonneg
  have hqq_nonneg : 0 ≤
      pom_multiplicity_composition_two_parameter_hessian_pd_entry_qq q * v ^ (2 : Nat) := by
    exact mul_nonneg hqq.le hv_sq_nonneg
  rcases huv with hu | hv
  · have hu_sq_pos : 0 < u ^ (2 : Nat) := by
      have hu_sq_ne : u ^ (2 : Nat) ≠ 0 := by
        exact pow_ne_zero 2 hu
      exact lt_of_le_of_ne hu_sq_nonneg (by simpa using hu_sq_ne.symm)
    have htt_pos : 0 <
        pom_multiplicity_composition_two_parameter_hessian_pd_entry_tt q * u ^ (2 : Nat) := by
      exact mul_pos htt hu_sq_pos
    unfold pom_multiplicity_composition_two_parameter_hessian_pd_quadratic_form
    linarith
  · have hv_sq_pos : 0 < v ^ (2 : Nat) := by
      have hv_sq_ne : v ^ (2 : Nat) ≠ 0 := by
        exact pow_ne_zero 2 hv
      exact lt_of_le_of_ne hv_sq_nonneg (by simpa using hv_sq_ne.symm)
    have hqq_pos : 0 <
        pom_multiplicity_composition_two_parameter_hessian_pd_entry_qq q * v ^ (2 : Nat) := by
      exact mul_pos hqq hv_sq_pos
    unfold pom_multiplicity_composition_two_parameter_hessian_pd_quadratic_form
    linarith

end

end Omega.POM
