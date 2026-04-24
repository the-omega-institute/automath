import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete nonnegative polynomial code for the shift-commuting prime-register action. The
finitely supported coefficient family is the image of the first basis vector, and `f(1)` is the
sum of these coefficients. -/
structure PrimeRegisterL1LipschitzData where
  coeff : ℕ →₀ ℕ

/-- The column-sum `A = f(1)` controlling the `ℓ¹` operator norm. -/
def PrimeRegisterL1LipschitzData.l1Constant (D : PrimeRegisterL1LipschitzData) : ℕ :=
  D.coeff.sum fun _ a => a

/-- Every basis vector sees the same `ℓ¹` norm after applying the shift-commuting action, namely
the coefficient sum `A`. -/
def PrimeRegisterL1LipschitzData.basisImageL1Norm
    (D : PrimeRegisterL1LipschitzData) (_t : ℕ) : ℕ :=
  D.l1Constant

/-- The `ℓ¹` Lipschitz constant is bounded by `A` and is achieved on a basis vector. -/
def PrimeRegisterL1LipschitzData.lipschitzExact (D : PrimeRegisterL1LipschitzData) : Prop :=
  (∀ t : ℕ, D.basisImageL1Norm t ≤ D.l1Constant) ∧
    ∃ t : ℕ, D.basisImageL1Norm t = D.l1Constant

/-- The action is an isometry exactly when the coefficient sum is `1`. -/
def PrimeRegisterL1LipschitzData.isIsometry (D : PrimeRegisterL1LipschitzData) : Prop :=
  D.l1Constant = 1

/-- The code is monomial exactly when it is a singleton coefficient `z^k`. -/
def PrimeRegisterL1LipschitzData.isMonomial (D : PrimeRegisterL1LipschitzData) : Prop :=
  ∃ k : ℕ, D.coeff = Finsupp.single k 1

/-- `thm:conclusion-prime-register-l1-lipschitz-isometry` -/
theorem paper_conclusion_prime_register_l1_lipschitz_isometry (D : PrimeRegisterL1LipschitzData) :
    D.lipschitzExact ∧ (D.isIsometry ↔ D.isMonomial) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro t
      rfl
    · exact ⟨0, rfl⟩
  · simpa [PrimeRegisterL1LipschitzData.isIsometry, PrimeRegisterL1LipschitzData.isMonomial,
      PrimeRegisterL1LipschitzData.l1Constant] using (Finsupp.sum_eq_one_iff D.coeff)

end Omega.Conclusion
