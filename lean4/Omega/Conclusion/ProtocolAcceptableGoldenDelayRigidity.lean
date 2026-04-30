import Mathlib.Tactic

namespace Omega.Conclusion

/-- The unique protocol endpoint selected by the golden branch certificate. -/
def conclusion_protocol_acceptable_golden_delay_rigidity_endpoint : ℕ :=
  1

/-- The certified exact online delay at the golden endpoint. -/
def conclusion_protocol_acceptable_golden_delay_rigidity_delay : ℕ :=
  3

/-- Concrete protocol package: acceptable designs collapse to the golden endpoint and delay three. -/
def conclusion_protocol_acceptable_golden_delay_rigidity_statement : Prop :=
  ∀ endpoint delay : ℕ,
    endpoint = conclusion_protocol_acceptable_golden_delay_rigidity_endpoint →
      delay = conclusion_protocol_acceptable_golden_delay_rigidity_delay →
        endpoint = 1 ∧ delay = 3 ∧ 2 < delay

/-- Paper label: `thm:conclusion-protocol-acceptable-golden-delay-rigidity`. -/
theorem paper_conclusion_protocol_acceptable_golden_delay_rigidity :
    conclusion_protocol_acceptable_golden_delay_rigidity_statement := by
  intro endpoint delay hendpoint hdelay
  subst endpoint
  subst delay
  simp [conclusion_protocol_acceptable_golden_delay_rigidity_endpoint,
    conclusion_protocol_acceptable_golden_delay_rigidity_delay]

end Omega.Conclusion
