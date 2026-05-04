import Mathlib.Tactic

namespace Omega.Conclusion

lemma conclusion_xi_dyadic_phase_governed_stability_controls
    (irrational_phase_changes rational_phase_periodic amplitude_controlled
      direction_uncontrolled : Prop)
    (hphase : irrational_phase_changes ∨ rational_phase_periodic)
    (hamp : irrational_phase_changes ∨ rational_phase_periodic → amplitude_controlled)
    (hdir : irrational_phase_changes ∨ rational_phase_periodic → direction_uncontrolled) :
    amplitude_controlled ∧ direction_uncontrolled := by
  exact ⟨hamp hphase, hdir hphase⟩

/-- Paper label: `cor:conclusion-xi-dyadic-phase-governed-stability`. -/
theorem paper_conclusion_xi_dyadic_phase_governed_stability
    (irrational_phase_changes rational_phase_periodic amplitude_controlled
      direction_uncontrolled : Prop)
    (hphase : irrational_phase_changes ∨ rational_phase_periodic)
    (hamp : irrational_phase_changes ∨ rational_phase_periodic → amplitude_controlled)
    (hdir : irrational_phase_changes ∨ rational_phase_periodic → direction_uncontrolled) :
    amplitude_controlled ∧ direction_uncontrolled := by
  exact conclusion_xi_dyadic_phase_governed_stability_controls
    irrational_phase_changes rational_phase_periodic amplitude_controlled direction_uncontrolled
    hphase hamp hdir

end Omega.Conclusion
