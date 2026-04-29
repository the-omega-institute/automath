import Mathlib.Data.Nat.Factorial.BigOperators

namespace Omega.Conclusion

/-- The product of factorial bucket sizes is bounded by the factorial of the total mass. -/
lemma conclusion_fiber_symmetry_entropy_extremals_factorial_prod_le_factorial_sum :
    ∀ multiplicity : List ℕ,
      (multiplicity.map Nat.factorial).prod ≤ Nat.factorial multiplicity.sum
  | [] => by simp
  | m :: multiplicity => by
      have htail :=
        conclusion_fiber_symmetry_entropy_extremals_factorial_prod_le_factorial_sum multiplicity
      calc
        ((m :: multiplicity).map Nat.factorial).prod =
            Nat.factorial m * (multiplicity.map Nat.factorial).prod := by
          simp
        _ ≤ Nat.factorial m * Nat.factorial multiplicity.sum := by
          exact Nat.mul_le_mul_left _ htail
        _ ≤ Nat.factorial (m + multiplicity.sum) := by
          exact Nat.le_of_dvd (Nat.factorial_pos _) <|
            Nat.factorial_mul_factorial_dvd_factorial_add m multiplicity.sum
        _ = Nat.factorial (m :: multiplicity).sum := by
          simp

/-- Each multiplicity bucket contributes at least one permutation. -/
lemma conclusion_fiber_symmetry_entropy_extremals_one_le_factorial_prod :
    ∀ multiplicity : List ℕ, 1 ≤ (multiplicity.map Nat.factorial).prod
  | [] => by simp
  | m :: multiplicity => by
      have htail :=
        conclusion_fiber_symmetry_entropy_extremals_one_le_factorial_prod multiplicity
      have hm : 1 ≤ Nat.factorial m := Nat.succ_le_of_lt (Nat.factorial_pos m)
      simpa using Nat.mul_le_mul hm htail

/-- Paper label: `thm:conclusion-fiber-symmetry-entropy-extremals`. -/
theorem paper_conclusion_fiber_symmetry_entropy_extremals (multiplicity : List ℕ) :
    let r := multiplicity.sum
    1 ≤ (multiplicity.map Nat.factorial).prod ∧
      (multiplicity.map Nat.factorial).prod ≤ Nat.factorial r ∧
        2 ^ r ≤ 2 ^ r * (multiplicity.map Nat.factorial).prod ∧
          2 ^ r * (multiplicity.map Nat.factorial).prod ≤ 2 ^ r * Nat.factorial r := by
  dsimp
  constructor
  · exact conclusion_fiber_symmetry_entropy_extremals_one_le_factorial_prod multiplicity
  constructor
  · exact conclusion_fiber_symmetry_entropy_extremals_factorial_prod_le_factorial_sum multiplicity
  constructor
  · simpa using Nat.mul_le_mul_left (2 ^ multiplicity.sum) <|
      conclusion_fiber_symmetry_entropy_extremals_one_le_factorial_prod multiplicity
  · exact Nat.mul_le_mul_left (2 ^ multiplicity.sum) <|
      conclusion_fiber_symmetry_entropy_extremals_factorial_prod_le_factorial_sum multiplicity

end Omega.Conclusion
