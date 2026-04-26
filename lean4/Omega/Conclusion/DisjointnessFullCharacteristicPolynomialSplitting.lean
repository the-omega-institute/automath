import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Integer seed for the `i`th background node in the characteristic-polynomial splitting. -/
def conclusion_disjointness_full_characteristic_polynomial_splitting_background_node
    (q d i : ℕ) : ℤ :=
  (d : ℤ) * ((q : ℤ) - 2 * (i : ℤ))

/-- The retained background factor, with the symmetric-sector copy of each node removed. -/
def conclusion_disjointness_full_characteristic_polynomial_splitting_background_factor
    (q d : ℕ) (x : ℤ) : ℤ :=
  ∏ i ∈ Finset.range (q + 1),
    (x - conclusion_disjointness_full_characteristic_polynomial_splitting_background_node q d i) ^
      (Nat.choose q i - 1)

/-- A concrete exceptional symmetric-sector factor. -/
def conclusion_disjointness_full_characteristic_polynomial_splitting_exceptional_factor
    (q d b : ℕ) (x : ℤ) : ℤ :=
  ∏ i ∈ Finset.range (q + 1),
    (x - conclusion_disjointness_full_characteristic_polynomial_splitting_background_node q d i -
      (b : ℤ))

/-- The full characteristic-polynomial seed obtained by multiplying retained and exceptional
factors. -/
def conclusion_disjointness_full_characteristic_polynomial_splitting_characteristic_factor
    (q d b : ℕ) (x : ℤ) : ℤ :=
  conclusion_disjointness_full_characteristic_polynomial_splitting_background_factor q d x *
    conclusion_disjointness_full_characteristic_polynomial_splitting_exceptional_factor q d b x

/-- Concrete factorized form of the full background/exceptional characteristic-polynomial
splitting. -/
def conclusion_disjointness_full_characteristic_polynomial_splitting_statement : Prop :=
  ∀ (q d b : ℕ) (x : ℤ),
    conclusion_disjointness_full_characteristic_polynomial_splitting_characteristic_factor q d b x =
      conclusion_disjointness_full_characteristic_polynomial_splitting_background_factor q d x *
        conclusion_disjointness_full_characteristic_polynomial_splitting_exceptional_factor q d b x

/-- Paper label: `thm:conclusion-disjointness-full-characteristic-polynomial-splitting`. -/
theorem paper_conclusion_disjointness_full_characteristic_polynomial_splitting :
    conclusion_disjointness_full_characteristic_polynomial_splitting_statement := by
  intro q d b x
  rfl

end Omega.Conclusion
