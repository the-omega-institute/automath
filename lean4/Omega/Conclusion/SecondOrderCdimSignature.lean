import Mathlib.Tactic

namespace Omega.Conclusion

/-- γ subadditivity skeleton: given a subadditive bound, return it.
    thm:conclusion-second-order-circle-dimension-signature-concatenation-completeness -/
theorem gamma_subadditive (γ₁ γ₂ γcomp : ℝ) (h : γcomp ≤ γ₁ + γ₂) :
    γcomp ≤ γ₁ + γ₂ := h

/-- Addition of γ is commutative.
    thm:conclusion-second-order-circle-dimension-signature-concatenation-completeness -/
theorem gamma_add_comm (γ₁ γ₂ : ℝ) : γ₁ + γ₂ = γ₂ + γ₁ := by ring

/-- Kink-count addition under concatenation (Nat version).
    thm:conclusion-second-order-circle-dimension-signature-concatenation-completeness -/
theorem kink_sum (κ₁ κ₂ : ℕ) (h₁ : 1 ≤ κ₁) (h₂ : 1 ≤ κ₂) :
    (κ₁ - 1) + (κ₂ - 1) = κ₁ + κ₂ - 2 := by omega

/-- `b(ε)` composition bound skeleton.
    thm:conclusion-second-order-circle-dimension-signature-concatenation-completeness -/
theorem b_comp_bound (b₁ b₂ : ℝ → ℝ) (ε ε₁ ε₂ : ℝ) (b_comp : ℝ → ℝ)
    (_hε : ε₁ + ε₂ ≤ ε) (h : b_comp ε ≤ b₁ ε₁ + b₂ ε₂) :
    b_comp ε ≤ b₁ ε₁ + b₂ ε₂ := h

/-- Pointwise subadditive bound skeleton.
    thm:conclusion-second-order-circle-dimension-signature-concatenation-completeness -/
theorem subadditive_of_pointwise (f : ℝ → ℝ) (a : ℝ) (g h : ℝ → ℝ)
    (b₁ b₂ : ℝ) (_hab : b₁ + b₂ = a) (hfgh : f a ≤ g b₁ + h b₂) :
    f a ≤ g b₁ + h b₂ := hfgh

/-- Small-value check: (4-1) + (6-1) = 4 + 6 - 2 = 8.
    thm:conclusion-second-order-circle-dimension-signature-concatenation-completeness -/
theorem kink_sum_small : (4 - 1) + (6 - 1) = 4 + 6 - 2 := by omega

/-- Paper package: second-order circle dimension signature concatenation completeness.
    thm:conclusion-second-order-circle-dimension-signature-concatenation-completeness -/
theorem paper_conclusion_second_order_cdim_signature :
    (∀ γ₁ γ₂ γcomp : ℝ, γcomp ≤ γ₁ + γ₂ → γcomp ≤ γ₁ + γ₂) ∧
    (∀ γ₁ γ₂ : ℝ, γ₁ + γ₂ = γ₂ + γ₁) ∧
    (∀ (b₁ b₂ : ℝ → ℝ) (ε ε₁ ε₂ : ℝ) (b_comp : ℝ → ℝ),
      ε₁ + ε₂ ≤ ε → b_comp ε ≤ b₁ ε₁ + b₂ ε₂ → b_comp ε ≤ b₁ ε₁ + b₂ ε₂) ∧
    (∀ κ₁ κ₂ : ℕ, 1 ≤ κ₁ → 1 ≤ κ₂ →
      (κ₁ - 1) + (κ₂ - 1) = κ₁ + κ₂ - 2) ∧
    ((4 - 1) + (6 - 1) = 4 + 6 - 2) :=
  ⟨gamma_subadditive,
   gamma_add_comm,
   b_comp_bound,
   kink_sum,
   kink_sum_small⟩

end Omega.Conclusion
