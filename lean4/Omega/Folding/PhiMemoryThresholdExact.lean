import Mathlib.Tactic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the exact one-sided memory threshold in the
    rigidity reconstruction section.
    cor:Phi-m-memory-threshold-exact -/
theorem paper_resolution_folding_phi_m_memory_threshold_exact
    (admissibleMemory : ℕ → Prop) {m : ℕ}
    (hWitness : admissibleMemory (m - 1))
    (hLower : ∀ n, admissibleMemory n → m - 1 ≤ n) :
    admissibleMemory (m - 1) ∧
      ∀ {n : ℕ}, admissibleMemory n → m - 1 ≤ n := by
  refine ⟨hWitness, ?_⟩
  intro n hn
  exact hLower n hn

end Omega.Folding
