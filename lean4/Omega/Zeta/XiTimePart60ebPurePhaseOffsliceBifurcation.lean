import Mathlib.Tactic

namespace Omega.Zeta

/-- The two permitted interface forms for a pure-phase off-slice assertion. -/
inductive xi_time_part60eb_pure_phase_offslice_bifurcation_offslice_form where
  | xi_time_part60eb_pure_phase_offslice_bifurcation_external_axis
  | xi_time_part60eb_pure_phase_offslice_bifurcation_null_failure_witness

/-- The explicit external-axis off-slice form. -/
abbrev xi_time_part60eb_pure_phase_offslice_bifurcation_external_axis_form :
    xi_time_part60eb_pure_phase_offslice_bifurcation_offslice_form :=
  .xi_time_part60eb_pure_phase_offslice_bifurcation_external_axis

/-- The `NULL` or failure-witness off-slice form. -/
abbrev xi_time_part60eb_pure_phase_offslice_bifurcation_null_failure_witness_form :
    xi_time_part60eb_pure_phase_offslice_bifurcation_offslice_form :=
  .xi_time_part60eb_pure_phase_offslice_bifurcation_null_failure_witness

/-- A finite mode budget is complete only if it bounds every finite horizon. -/
def xi_time_part60eb_pure_phase_offslice_bifurcation_finite_mode_budget_complete
    (budget : ℕ) : Prop :=
  ∀ horizon : ℕ, horizon ≤ budget

/-- The finite-budget obstruction: no fixed budget bounds all finite horizons. -/
def xi_time_part60eb_pure_phase_offslice_bifurcation_busy_beaver_obstruction : Prop :=
  ∀ budget : ℕ,
    ¬ xi_time_part60eb_pure_phase_offslice_bifurcation_finite_mode_budget_complete budget

/-- Paper label: `thm:xi-time-part60eb-pure-phase-offslice-bifurcation`. -/
def xi_time_part60eb_pure_phase_offslice_bifurcation_statement : Prop :=
  (∀ form : xi_time_part60eb_pure_phase_offslice_bifurcation_offslice_form,
      form = xi_time_part60eb_pure_phase_offslice_bifurcation_external_axis_form ∨
        form = xi_time_part60eb_pure_phase_offslice_bifurcation_null_failure_witness_form) ∧
    (¬ ∃ form : xi_time_part60eb_pure_phase_offslice_bifurcation_offslice_form,
      form ≠ xi_time_part60eb_pure_phase_offslice_bifurcation_external_axis_form ∧
        form ≠ xi_time_part60eb_pure_phase_offslice_bifurcation_null_failure_witness_form ∧
          True) ∧
    xi_time_part60eb_pure_phase_offslice_bifurcation_busy_beaver_obstruction

/-- Paper label: `thm:xi-time-part60eb-pure-phase-offslice-bifurcation`. -/
theorem paper_xi_time_part60eb_pure_phase_offslice_bifurcation :
    xi_time_part60eb_pure_phase_offslice_bifurcation_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro form
    cases form <;> simp
  · rintro ⟨form, hnot_external, hnot_null, -⟩
    cases form
    · exact hnot_external rfl
    · exact hnot_null rfl
  · intro budget hcomplete
    have hbad : budget + 1 ≤ budget := hcomplete (budget + 1)
    omega

end Omega.Zeta
