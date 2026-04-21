import Omega.Conclusion.MultishiftCommutingAlgorithmsPolynomial

namespace Omega.Conclusion

/-- The origin basis image already determines the multishift coefficient family. -/
def multishiftRandomWalkCoefficientLaw (d : ℕ) : Prop :=
  ∀ f : MultishiftPolynomial d, ∃! c : MultishiftPolynomial d,
    multishiftBasisImage c 0 = multishiftBasisImage f 0

/-- Starting from the origin basis vector, the `n`-step multishift profile is exactly `f^n`. -/
def multishiftRandomWalkLargeNumbersLaw (d : ℕ) : Prop :=
  ∀ f : MultishiftPolynomial d, ∀ n : ℕ, multishiftBasisImage (f ^ n) 0 = f ^ n

/-- One extra multishift step multiplies the current profile by the same coefficient family. -/
def multishiftRandomWalkCentralLimitLaw (d : ℕ) : Prop :=
  ∀ f : MultishiftPolynomial d, ∀ n : ℕ,
    multishiftBasisImage (f ^ (n + 1)) 0 = multishiftBasisImage (f ^ n) 0 * f

/-- Paper label: `thm:conclusion-multishift-random-walk-profile`. The multishift polynomial model
already packages the coefficient law and the one-step profile recursion for iterates from the
origin basis vector. -/
theorem paper_conclusion_multishift_random_walk_profile (d : ℕ) :
    multishiftRandomWalkCoefficientLaw d ∧
      multishiftRandomWalkLargeNumbersLaw d ∧
      multishiftRandomWalkCentralLimitLaw d := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    exact (paper_conclusion_multishift_commuting_algorithms_polynomial d f f).1
  · intro f n
    change (1 : MultishiftPolynomial d) * f ^ n = f ^ n
    exact one_mul (f ^ n)
  · intro f n
    change (1 : MultishiftPolynomial d) * f ^ (n + 1) = ((1 : MultishiftPolynomial d) * f ^ n) * f
    rw [one_mul, one_mul, pow_succ]

end Omega.Conclusion
