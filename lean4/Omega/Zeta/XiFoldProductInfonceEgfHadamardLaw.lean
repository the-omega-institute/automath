import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-product-infonce-egf-hadamard-law`. -/
theorem paper_xi_fold_product_infonce_egf_hadamard_law (a p₁ p₂ : ℕ → ℝ) :
    (let hadamard := fun u v : ℕ → ℝ => fun r => u r * v r
     let kernel := fun p : ℕ → ℝ => fun r => a r * p r
     kernel (hadamard p₁ p₂) = hadamard a (hadamard p₁ p₂)) := by
  rfl

end Omega.Zeta
