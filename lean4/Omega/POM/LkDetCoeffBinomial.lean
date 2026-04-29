import Omega.Folding.FibonacciPolynomial

namespace Omega

/-- Paper wrapper for the determinant-polynomial binomial coefficient package.
    prop:pom-Lk-det-coeff-binomial -/
theorem paper_pom_lk_det_coeff_binomial (k : ℕ) :
    (detPoly k).Monic ∧ (detPoly k).natDegree = k ∧
      (∀ j, j ≤ k → (detPoly k).coeff j = (Nat.choose (k + j) (2 * j) : ℤ)) ∧
      (∀ j, j ≤ k → 0 < (detPoly k).coeff j) ∧ (detPoly k).coeff 0 = 1 ∧
      (1 ≤ k → (detPoly k).coeff (k - 1) = (2 * k - 1 : ℤ)) ∧
      (detPoly k).coeff k = 1 := by
  refine ⟨detPoly_monic k, detPoly_natDegree k, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact detPoly_coeff_binomial k j hj
  · intro j hj
    exact detPoly_coeff_pos k j hj
  · simpa using detPoly_coeff_binomial k 0 (Nat.zero_le k)
  · intro hk
    exact detPoly_coeff_sub_leading k hk
  · have h := detPoly_coeff_binomial k k le_rfl
    rw [show k + k = 2 * k by omega] at h
    simpa using h

end Omega
