import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-finite-state-gate-fragment-decidable-order-gate-role`. The finite-state closure and
decidability hypotheses package together with the undecidability obstruction to rule out semantic
Turing completeness, while preserving the stated order-gate depth fact. -/
theorem paper_conclusion_finite_state_gate_fragment_decidable_order_gate_role
    (finiteStateClosure semanticEquivalenceDecidable semanticTuringComplete
      orderGateLinearDepth : Prop)
    (hclosure : finiteStateClosure)
    (hdecide : finiteStateClosure → semanticEquivalenceDecidable)
    (hundecidable : semanticTuringComplete → ¬ semanticEquivalenceDecidable)
    (horder : orderGateLinearDepth) :
    finiteStateClosure ∧ semanticEquivalenceDecidable ∧ ¬ semanticTuringComplete ∧
      orderGateLinearDepth := by
  refine ⟨hclosure, hdecide hclosure, ?_, horder⟩
  intro htc
  exact hundecidable htc (hdecide hclosure)

end Omega.Conclusion
