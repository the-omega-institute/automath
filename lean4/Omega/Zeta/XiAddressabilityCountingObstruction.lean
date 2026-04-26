import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete counting model for the finite-generation obstruction: a finitely generated
addressability mechanism would force an eventual linear bound with a fixed constant, while the
classical zeta zero count eventually beats every such linear model. -/
structure xi_addressability_counting_obstruction_data where
  zero_count : ℕ → ℕ
  strip_linear_constant : ℕ
  classical_superlinear :
    ∀ C T0 : ℕ, ∃ T ≥ T0, C * T < zero_count T

/-- Eventual `O(T)` growth in a fixed strip, as predicted by a finitely generated addressability
model. -/
def xi_addressability_counting_obstruction_data.finitely_generated_addressable
    (D : xi_addressability_counting_obstruction_data) : Prop :=
  ∃ T0 : ℕ, ∀ T ≥ T0, D.zero_count T ≤ D.strip_linear_constant * T

/-- Paper label: `prop:xi-addressability-counting-obstruction`.
Any finite-generation addressability model yields eventual linear growth in height, but the
classical zeta zero count eventually dominates every linear function. -/
theorem paper_xi_addressability_counting_obstruction
    (D : xi_addressability_counting_obstruction_data) : ¬ D.finitely_generated_addressable := by
  intro hfg
  rcases hfg with ⟨T0, hT0⟩
  rcases D.classical_superlinear D.strip_linear_constant T0 with ⟨T, hTge, hTlt⟩
  have hbound : D.zero_count T ≤ D.strip_linear_constant * T := hT0 T hTge
  exact (Nat.not_lt_of_ge hbound) hTlt

end Omega.Zeta
