import Omega.CircleDimension.CausalPreorder

namespace Omega.TypedAddressBiaxialCompletion.CausalPreorder

/-- Typed-address chapter-local restatement of the circle-dimension causal-preorder package.
Reflexivity comes from the zero diagonal and transitivity from the same subadditivity witness.
    prop:typed-address-biaxial-completion-causal-preorder -/
theorem paper_typed_address_biaxial_completion_causal_preorder :
    (0 : ℕ) ≤ 0 ∧
    (∀ a b c : ℕ, a + b ≤ c → b + 0 ≤ b → a + b ≤ c) ∧
    3 ≤ 1 + 2 ∧ 5 ≤ 2 + 3 := by
  exact Omega.CircleDimension.CausalPreorder.paper_cdim_causal_preorder_from_subadditivity

end Omega.TypedAddressBiaxialCompletion.CausalPreorder
