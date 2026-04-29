import Mathlib.Tactic

namespace Omega.Conclusion

/-- Abel finite-part displacement at the endpoint, after substituting the zero-temperature
ground-state scale. -/
noncomputable def conclusion_realinput40_zero_temp_finitepart_displacement_endpoint
    (c : ℝ) : ℝ :=
  1 * c⁻¹ ^ 2

/-- Perron separation certificate: the limiting displacement equals the inverse Perron root
when the Perron root is `c^2`. -/
def conclusion_realinput40_zero_temp_finitepart_displacement_statement : Prop :=
  ∀ c rhoB : ℝ,
    c ≠ 0 →
      rhoB = c ^ 2 →
        conclusion_realinput40_zero_temp_finitepart_displacement_endpoint c = rhoB⁻¹

/-- Paper label: `cor:conclusion-realinput40-zero-temp-finitepart-displacement`. -/
theorem paper_conclusion_realinput40_zero_temp_finitepart_displacement :
    conclusion_realinput40_zero_temp_finitepart_displacement_statement := by
  intro c rhoB hc hrho
  subst rhoB
  unfold conclusion_realinput40_zero_temp_finitepart_displacement_endpoint
  field_simp [hc]

end Omega.Conclusion
