import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

universe u v

/-- Deterministic certificate backend for the two-integer unitary routine. `certify` computes the
output attached to an input, while `replay` rechecks that output from the same input data. -/
structure UnitaryTwoIntegerCertificateConfig (α : Type u) where
  Output : Type v
  certify : α → Output
  replay : α → Output → Prop
  replay_certify : ∀ u, replay u (certify u)

/-- Paper label: `prop:unitary-two-integer-reproducible`. A deterministic certificate backend is
reproducible because the input fixes the computed output, and replay is just recomputation on
that same output. -/
theorem paper_unitary_two_integer_reproducible {α : Type u}
    (cfg : UnitaryTwoIntegerCertificateConfig α) (u : α) :
    ∃! out, cfg.certify u = out ∧ cfg.replay u out := by
  refine ⟨cfg.certify u, ?_, ?_⟩
  · exact ⟨rfl, cfg.replay_certify u⟩
  · intro out hout
    exact hout.1.symm

end Omega.UnitCirclePhaseArithmetic
