import Mathlib.Tactic

namespace Omega.Conclusion

/-- Finite-prime selector products multiply independently across the coordinates, so raising the
single-coordinate selector product to the `r`th power exactly reproduces the joint law.
    thm:conclusion-boundary-finite-prime-selector-product-law -/
theorem paper_conclusion_boundary_finite_prime_selector_product_law {ι : Type} [Fintype ι]
    (p ell : ι → ℕ) (r : ℕ) : (∏ i, p i ^ (ell i * r)) = (∏ i, p i ^ ell i) ^ r := by
  classical
  calc
    (∏ i, p i ^ (ell i * r)) = ∏ i, (p i ^ ell i) ^ r := by
      simp_rw [pow_mul]
    _ = (∏ i, p i ^ ell i) ^ r := by
      exact (map_prod (powMonoidHom r : ℕ →* ℕ) (fun i => p i ^ ell i) Finset.univ).symm

end Omega.Conclusion
