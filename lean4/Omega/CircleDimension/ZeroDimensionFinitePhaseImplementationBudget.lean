import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- A zero-dimensional finite phase implementation can distinguish at most `Q^k` quantized outputs.
    thm:cdim-zero-dimension-finite-phase-implementation-budget -/
theorem paper_cdim_zero_dimension_finite_phase_implementation_budget (M Q k : Nat)
    (henc : ∃ f : Fin M → Fin (Q ^ k), Function.Injective f) : M <= Q ^ k := by
  rcases henc with ⟨f, hf⟩
  simpa using Fintype.card_le_of_injective f hf

end Omega.CircleDimension
