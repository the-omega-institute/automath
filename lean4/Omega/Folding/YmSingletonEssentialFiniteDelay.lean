import Omega.Graph.PhiGraph
import Mathlib.Tactic

namespace Omega.Folding

/-- If the two outgoing labels at each state are distinct, then there is a per-state decoder that
    recovers the emitted bit and therefore reproduces the same state transition.
    cor:Ym-singleton-essential-finite-delay -/
theorem paper_Ym_singleton_essential_finite_delay {m : ℕ} {α : Type*}
    (emit : Omega.Graph.PhiState m → Bool → α)
    (step : Omega.Graph.PhiState m → Bool → Omega.Graph.PhiState m)
    (hSep : ∀ v, emit v false ≠ emit v true) :
    ∃ decode : Omega.Graph.PhiState m → α → Bool,
      (∀ v b, decode v (emit v b) = b) ∧
      (∀ v b, step v (decode v (emit v b)) = step v b) := by
  classical
  let decode : Omega.Graph.PhiState m → α → Bool :=
    fun v a => if a = emit v false then false else true
  have hdecode : ∀ v b, decode v (emit v b) = b := by
    intro v b
    cases b <;> simp [decode, hSep v, eq_comm]
  refine ⟨decode, hdecode, ?_⟩
  intro v b
  rw [hdecode v b]

end Omega.Folding
