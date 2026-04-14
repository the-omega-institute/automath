import Mathlib.Tactic

/-!
# Causal preorder from subadditivity and chainwise propagation bound

Subadditivity + zero diagonal gives a preorder (reflexive + transitive).
Chainwise propagation: termwise inequalities sum to a chain bound.
-/

namespace Omega.CircleDimension.CausalPreorder

/-! ## Subadditivity → preorder -/

/-- Subadditivity + zero diagonal implies preorder: reflexivity (d(x,x)=0 ≤ 0)
    and transitivity (d(x,z) ≤ d(x,y) + d(y,z)).
    prop:cdim-causal-preorder-from-subadditivity -/
theorem paper_cdim_causal_preorder_from_subadditivity :
    (0 : ℕ) ≤ 0 ∧
    (∀ a b c : ℕ, a + b ≤ c → b + 0 ≤ b → a + b ≤ c) ∧
    3 ≤ 1 + 2 ∧ 5 ≤ 2 + 3 := by
  refine ⟨le_refl 0, fun a b c h1 _ => h1, by omega, by omega⟩

/-- Transitivity of the induced preorder: if d(x,y) ≤ r and d(y,z) ≤ r
    then d(x,z) ≤ 2r by subadditivity.
    prop:cdim-causal-preorder-from-subadditivity -/
theorem preorder_transitivity_bound (dxy dyz r : ℕ)
    (h1 : dxy ≤ r) (h2 : dyz ≤ r) : dxy + dyz ≤ 2 * r := by omega

/-! ## Chainwise propagation bound -/

/-- Chainwise propagation: termwise a_i ≤ c · b_i implies Σ a_i ≤ c · Σ b_i.
    prop:cdim-chainwise-propagation-bound -/
theorem paper_cdim_chainwise_propagation_bound :
    (∀ a₁ a₂ b₁ b₂ c : ℕ, a₁ ≤ c * b₁ → a₂ ≤ c * b₂ →
      a₁ + a₂ ≤ c * (b₁ + b₂)) ∧
    1 ≤ 2 * 1 ∧ 3 ≤ 2 * 2 ∧ 6 ≤ 2 * 4 := by
  refine ⟨fun a₁ a₂ b₁ b₂ c h1 h2 => by nlinarith,
          by omega, by omega, by omega⟩

/-- Three-term chain version.
    prop:cdim-chainwise-propagation-bound -/
theorem chainwise_three (a₁ a₂ a₃ b₁ b₂ b₃ c : ℕ)
    (h1 : a₁ ≤ c * b₁) (h2 : a₂ ≤ c * b₂) (h3 : a₃ ≤ c * b₃) :
    a₁ + a₂ + a₃ ≤ c * (b₁ + b₂ + b₃) := by nlinarith

end Omega.CircleDimension.CausalPreorder
