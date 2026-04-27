import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the q-axis divisor specialization of the Ramanujan Parseval control bound. -/
structure conclusion_qaxis_cumulative_atomic_signal_uniform_parseval_bound_Data where
  q : ℕ
  boundaryEnergy : ℝ
  qAxisSignal : ℝ
  parsevalMass : ℝ
  baselConstant : ℝ
  boundaryEnergy_nonneg : 0 ≤ boundaryEnergy
  ramanujan_parseval_control : qAxisSignal ^ 2 ≤ parsevalMass * boundaryEnergy
  qaxis_parseval_identity : parsevalMass = baselConstant
  basel_constant_bound : baselConstant ≤ Real.pi ^ 2 / 6

/-- The specialized q-axis cumulative atomic signal obeys the uniform Basel/Parseval bound. -/
def conclusion_qaxis_cumulative_atomic_signal_uniform_parseval_bound_statement
    (D : conclusion_qaxis_cumulative_atomic_signal_uniform_parseval_bound_Data) : Prop :=
  D.qAxisSignal ^ 2 ≤ (Real.pi ^ 2 / 6) * D.boundaryEnergy

/-- Paper label: `cor:conclusion-qaxis-cumulative-atomic-signal-uniform-parseval-bound`. -/
theorem paper_conclusion_qaxis_cumulative_atomic_signal_uniform_parseval_bound
    (D : conclusion_qaxis_cumulative_atomic_signal_uniform_parseval_bound_Data) :
    conclusion_qaxis_cumulative_atomic_signal_uniform_parseval_bound_statement D := by
  have hmass_le : D.parsevalMass ≤ Real.pi ^ 2 / 6 := by
    simpa [D.qaxis_parseval_identity] using D.basel_constant_bound
  exact le_trans D.ramanujan_parseval_control
    (mul_le_mul_of_nonneg_right hmass_le D.boundaryEnergy_nonneg)

end Omega.Conclusion
