import Mathlib.Data.Real.Basic

namespace Omega.GU

/-- Paper-facing jet-alignment certificate: if all active channels agree on value, first
derivative, and second derivative, then the three alignment clauses hold simultaneously.
    prop:jet-alignment-unification -/
theorem paper_jet_alignment_unification {ι : Type} (g0 g1 g2 : ι → ℝ)
    (h0 : ∀ i j, g0 i = g0 j) (h1 : ∀ i j, g1 i = g1 j) (h2 : ∀ i j, g2 i = g2 j) :
    (∀ i j, g0 i = g0 j) ∧ (∀ i j, g1 i = g1 j) ∧ (∀ i j, g2 i = g2 j) := by
  exact ⟨h0, h1, h2⟩

end Omega.GU
