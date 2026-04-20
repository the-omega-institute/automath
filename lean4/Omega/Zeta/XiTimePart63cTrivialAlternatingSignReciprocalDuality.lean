import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Rewriting `H (-z)` turns each factor into `(1 + d x * z)⁻¹`, and the finite product is then
the inverse of the alternating-channel product.
    thm:xi-time-part63c-trivial-alternating-sign-reciprocal-duality -/
theorem paper_xi_time_part63c_trivial_alternating_sign_reciprocal_duality
    {α : Type} [Fintype α] (H E : ℝ → ℝ) (d : α → ℝ)
    (hH : ∀ z, H z = ∏ x, (1 - d x * z)⁻¹)
    (hE : ∀ z, E z = ∏ x, (1 + d x * z)) :
    ∀ z, E z = (H (-z))⁻¹ := by
  classical
  intro z
  rw [hE z, hH (-z)]
  have hprod :
      ∏ x, (1 - d x * (-z))⁻¹ = ∏ x, (1 + d x * z)⁻¹ := by
    refine Finset.prod_congr rfl ?_
    intro x hx
    ring_nf
  calc
    ∏ x, (1 + d x * z) = ((∏ x, (1 + d x * z)⁻¹)⁻¹) := by
      rw [← Finset.prod_inv_distrib]
      simp
    _ = (∏ x, (1 - d x * (-z))⁻¹)⁻¹ := by rw [hprod]

end Omega.Zeta
