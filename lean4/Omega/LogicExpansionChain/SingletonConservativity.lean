import Mathlib.Tactic

namespace Omega.LogicExpansionChain.SingletonConservativity

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: forcing over a singleton state is conservative over point semantics.
    prop:logic-expansion-singleton-conservativity -/
theorem paper_logic_expansion_singleton_conservativity_seeds
    {Val Formula : Type} (satisfies : Val → Formula → Prop)
    (ρ : Val) (φ : Formula) :
    (∀ σ ∈ ({ρ} : Set Val), satisfies σ φ) ↔ satisfies ρ φ := by
  simp

/-- Wrapper theorem matching the paper-facing package name.
    prop:logic-expansion-singleton-conservativity -/
theorem paper_logic_expansion_singleton_conservativity_package
    {Val Formula : Type} (satisfies : Val → Formula → Prop)
    (ρ : Val) (φ : Formula) :
    (∀ σ ∈ ({ρ} : Set Val), satisfies σ φ) ↔ satisfies ρ φ :=
  paper_logic_expansion_singleton_conservativity_seeds satisfies ρ φ

end Omega.LogicExpansionChain.SingletonConservativity
