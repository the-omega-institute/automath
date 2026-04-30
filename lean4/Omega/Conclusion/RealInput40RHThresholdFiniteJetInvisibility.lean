import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic
import Omega.Conclusion.RealInput40LegendreQuadraticFieldRigidity
import Omega.Zeta.XiTimePart9pbRhCriticalQuinticField

namespace Omega.Conclusion

/-- The formal quadratic-field closure of finite local cumulant jets. -/
abbrev conclusion_realinput40_rh_threshold_finite_jet_invisibility_finite_jet_closure :=
  ℚ × ℚ

/-- Evaluation of a finite-jet closure element in `ℚ(√5)`. -/
noncomputable def conclusion_realinput40_rh_threshold_finite_jet_invisibility_closure_value
    (x : conclusion_realinput40_rh_threshold_finite_jet_invisibility_finite_jet_closure) :
    ℝ :=
  (x.1 : ℝ) + (x.2 : ℝ) * Real.sqrt 5

/-- Degree of the RH-threshold quintic certificate. -/
def conclusion_realinput40_rh_threshold_finite_jet_invisibility_threshold_degree : ℕ :=
  Omega.Zeta.xi_time_part9pb_rh_critical_quintic_field_degree

/-- Degree bound for values living in the quadratic finite-jet closure. -/
def conclusion_realinput40_rh_threshold_finite_jet_invisibility_quadratic_degree : ℕ :=
  2

/-- Paper-facing finite-jet invisibility statement: finite jets remain in the quadratic closure,
whereas the RH threshold carries degree `5`, so the degree-divisibility obstruction rules out
equality. -/
def conclusion_realinput40_rh_threshold_finite_jet_invisibility_statement : Prop :=
  (∀ x : conclusion_realinput40_rh_threshold_finite_jet_invisibility_finite_jet_closure,
      ∃ a b : ℚ,
        conclusion_realinput40_rh_threshold_finite_jet_invisibility_closure_value x =
          (a : ℝ) + (b : ℝ) * Real.sqrt 5) ∧
    conclusion_realinput40_rh_threshold_finite_jet_invisibility_threshold_degree = 5 ∧
    conclusion_realinput40_rh_threshold_finite_jet_invisibility_quadratic_degree = 2 ∧
    ¬ conclusion_realinput40_rh_threshold_finite_jet_invisibility_threshold_degree ∣
      conclusion_realinput40_rh_threshold_finite_jet_invisibility_quadratic_degree ∧
    (∀ d : ℕ,
      d ∣ conclusion_realinput40_rh_threshold_finite_jet_invisibility_quadratic_degree →
        d = conclusion_realinput40_rh_threshold_finite_jet_invisibility_threshold_degree →
          False) ∧
    Omega.Zeta.xi_time_part9pb_rh_critical_quintic_field_statement ∧
    conclusion_realinput40_legendre_quadratic_field_rigidity_statement

/-- Paper label: `thm:conclusion-realinput40-rh-threshold-finite-jet-invisibility`. -/
theorem paper_conclusion_realinput40_rh_threshold_finite_jet_invisibility :
    conclusion_realinput40_rh_threshold_finite_jet_invisibility_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨x.1, x.2, rfl⟩
  · rfl
  · rfl
  · norm_num [conclusion_realinput40_rh_threshold_finite_jet_invisibility_threshold_degree,
      conclusion_realinput40_rh_threshold_finite_jet_invisibility_quadratic_degree,
      Omega.Zeta.xi_time_part9pb_rh_critical_quintic_field_degree]
  · intro d hd hd_eq
    have hnot :
        ¬ conclusion_realinput40_rh_threshold_finite_jet_invisibility_threshold_degree ∣
          conclusion_realinput40_rh_threshold_finite_jet_invisibility_quadratic_degree := by
      norm_num [conclusion_realinput40_rh_threshold_finite_jet_invisibility_threshold_degree,
        conclusion_realinput40_rh_threshold_finite_jet_invisibility_quadratic_degree,
        Omega.Zeta.xi_time_part9pb_rh_critical_quintic_field_degree]
    exact hnot (by simpa [hd_eq] using hd)
  · exact Omega.Zeta.paper_xi_time_part9pb_rh_critical_quintic_field
  · exact conclusion_realinput40_legendre_quadratic_field_rigidity_holds

end Omega.Conclusion
