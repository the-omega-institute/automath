import Omega.Conclusion.FiniteStateGateFragmentDecidableOrderGateRole

set_option linter.unusedVariables false

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-bounded-order-projection-finite-state-collapse`.

A bounded order gate supplies a finite-resolution readout, and the finite-state gate fragment
obstruction rules out semantic Turing completeness once semantic equivalence is decidable. -/
theorem paper_conclusion_bounded_order_projection_finite_state_collapse
    (b : ℕ)
    (boundedGate finiteStateClosure semanticEquivalenceDecidable semanticTuringComplete : Prop)
    (hbounded : ∃ m : ℕ, boundedGate)
    (hclosure : finiteStateClosure)
    (hdecide : finiteStateClosure → semanticEquivalenceDecidable)
    (hundecidable : semanticTuringComplete → ¬ semanticEquivalenceDecidable) :
    (∃ m : ℕ, boundedGate) ∧ finiteStateClosure ∧ semanticEquivalenceDecidable ∧
      ¬ semanticTuringComplete := by
  have hfragment :=
    paper_conclusion_finite_state_gate_fragment_decidable_order_gate_role
      finiteStateClosure semanticEquivalenceDecidable semanticTuringComplete
      (∃ m : ℕ, boundedGate) hclosure hdecide hundecidable hbounded
  rcases hfragment with ⟨hclosure', hsemantic, hnotComplete, _⟩
  exact ⟨hbounded, hclosure', hsemantic, hnotComplete⟩

end Omega.Conclusion
