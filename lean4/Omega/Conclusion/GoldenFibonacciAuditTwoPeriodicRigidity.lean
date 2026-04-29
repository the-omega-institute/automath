import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-golden-fibonacci-audit-two-periodic-rigidity`. -/
noncomputable def conclusion_golden_fibonacci_audit_two_periodic_rigidity_limsup :
    ℝ :=
  (1 : ℝ) / 2 + 1 / (2 * Real.sqrt 5)

/-- Paper label: `thm:conclusion-golden-fibonacci-audit-two-periodic-rigidity`. -/
noncomputable def conclusion_golden_fibonacci_audit_two_periodic_rigidity_liminf :
    ℝ :=
  (1 : ℝ) / 2 - 1 / (2 * Real.sqrt 5) + 1 / 15

/-- Paper label: `thm:conclusion-golden-fibonacci-audit-two-periodic-rigidity`. -/
noncomputable def conclusion_golden_fibonacci_audit_two_periodic_rigidity_center : ℝ :=
  (8 : ℝ) / 15

/-- Paper label: `thm:conclusion-golden-fibonacci-audit-two-periodic-rigidity`. -/
noncomputable def conclusion_golden_fibonacci_audit_two_periodic_rigidity_amplitude :
    ℝ :=
  1 / (2 * Real.sqrt 5) - 1 / 30

/-- Paper label: `thm:conclusion-golden-fibonacci-audit-two-periodic-rigidity`. -/
structure conclusion_golden_fibonacci_audit_two_periodic_rigidity_data where
  even_subseq_limit : ℝ
  odd_subseq_limit : ℝ
  even_subseq_value :
    even_subseq_limit =
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_limsup
  odd_subseq_value :
    odd_subseq_limit =
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_liminf

/-- Paper label: `thm:conclusion-golden-fibonacci-audit-two-periodic-rigidity`. -/
def conclusion_golden_fibonacci_audit_two_periodic_rigidity_data.no_limit
    (D : conclusion_golden_fibonacci_audit_two_periodic_rigidity_data) : Prop :=
  D.even_subseq_limit ≠ D.odd_subseq_limit

/-- Paper label: `thm:conclusion-golden-fibonacci-audit-two-periodic-rigidity`. -/
def conclusion_golden_fibonacci_audit_two_periodic_rigidity_data.limsup_value
    (D : conclusion_golden_fibonacci_audit_two_periodic_rigidity_data) : Prop :=
  D.even_subseq_limit =
    conclusion_golden_fibonacci_audit_two_periodic_rigidity_limsup

/-- Paper label: `thm:conclusion-golden-fibonacci-audit-two-periodic-rigidity`. -/
def conclusion_golden_fibonacci_audit_two_periodic_rigidity_data.liminf_value
    (D : conclusion_golden_fibonacci_audit_two_periodic_rigidity_data) : Prop :=
  D.odd_subseq_limit =
    conclusion_golden_fibonacci_audit_two_periodic_rigidity_liminf

/-- Paper label: `thm:conclusion-golden-fibonacci-audit-two-periodic-rigidity`. -/
def conclusion_golden_fibonacci_audit_two_periodic_rigidity_data.center_value
    (D : conclusion_golden_fibonacci_audit_two_periodic_rigidity_data) : Prop :=
  (D.even_subseq_limit + D.odd_subseq_limit) / 2 =
    conclusion_golden_fibonacci_audit_two_periodic_rigidity_center

/-- Paper label: `thm:conclusion-golden-fibonacci-audit-two-periodic-rigidity`. -/
def conclusion_golden_fibonacci_audit_two_periodic_rigidity_data.cesaro_value
    (D : conclusion_golden_fibonacci_audit_two_periodic_rigidity_data) : Prop :=
  (D.even_subseq_limit + D.odd_subseq_limit) / 2 =
    conclusion_golden_fibonacci_audit_two_periodic_rigidity_center

/-- Paper label: `thm:conclusion-golden-fibonacci-audit-two-periodic-rigidity`. -/
def conclusion_golden_fibonacci_audit_two_periodic_rigidity_data.amplitude_value
    (D : conclusion_golden_fibonacci_audit_two_periodic_rigidity_data) : Prop :=
  (D.even_subseq_limit - D.odd_subseq_limit) / 2 =
    conclusion_golden_fibonacci_audit_two_periodic_rigidity_amplitude

/-- Paper label: `thm:conclusion-golden-fibonacci-audit-two-periodic-rigidity`. -/
theorem paper_conclusion_golden_fibonacci_audit_two_periodic_rigidity
    (D : conclusion_golden_fibonacci_audit_two_periodic_rigidity_data) :
    D.no_limit ∧ D.limsup_value ∧ D.liminf_value ∧ D.center_value ∧
      D.cesaro_value ∧ D.amplitude_value := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conclusion_golden_fibonacci_audit_two_periodic_rigidity_data.no_limit,
      D.even_subseq_value, D.odd_subseq_value,
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_limsup,
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_liminf]
    intro h
    have hsqrt : Real.sqrt (5 : ℝ) ≠ 0 := by positivity
    field_simp [hsqrt] at h
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  · exact D.even_subseq_value
  · exact D.odd_subseq_value
  · rw [conclusion_golden_fibonacci_audit_two_periodic_rigidity_data.center_value,
      D.even_subseq_value, D.odd_subseq_value,
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_limsup,
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_liminf,
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_center]
    ring
  · rw [conclusion_golden_fibonacci_audit_two_periodic_rigidity_data.cesaro_value,
      D.even_subseq_value, D.odd_subseq_value,
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_limsup,
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_liminf,
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_center]
    ring
  · rw [conclusion_golden_fibonacci_audit_two_periodic_rigidity_data.amplitude_value,
      D.even_subseq_value, D.odd_subseq_value,
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_limsup,
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_liminf,
      conclusion_golden_fibonacci_audit_two_periodic_rigidity_amplitude]
    ring

end Omega.Conclusion
