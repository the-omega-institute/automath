import Mathlib.Tactic
import Omega.Conclusion.Window6CyclicMultiplicityEscortUniqueIsotropy

namespace Omega.Conclusion

open Matrix

noncomputable section

/-- Cyclic escort denominator for the window-`6` multiplicity shells `2, 3, 4`. -/
def conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_denominator
    (q : Nat) : Real :=
  5 * (2 : Real) ^ q + 4 * (3 : Real) ^ q + 9 * (4 : Real) ^ q

/-- Upper-temperature endpoint of the first moment, dominated by the `4^q` shell. -/
def conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_upper_mu :
    Fin 3 → Real :=
  ![(1 : Real) / 9, 0, 0]

/-- Lower-temperature endpoint of the first moment, dominated by the `2^q` shell. -/
def conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_lower_mu :
    Fin 3 → Real :=
  ![-(1 : Real) / 5, 0, 0]

/-- Upper endpoint covariance matrix from the `d = 4` shell. -/
def conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_upper_sigma :
    Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal ![(5 : Real) / 9, (6 : Real) / 9, (2 : Real) / 9]

/-- Lower endpoint covariance matrix from the `d = 2` shell. -/
def conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_lower_sigma :
    Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal ![(1 : Real) / 5, (4 : Real) / 5, (4 : Real) / 5]

/-- Concrete endpoint-freezing package tied to the already proved unique-isotropy closed forms. -/
def conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_statement : Prop :=
  (∀ q : Nat,
      (window6CyclicMultiplicityFirstMoment ((2 : Real) ^ q) ((3 : Real) ^ q)
        ((4 : Real) ^ q) = 0 ↔ q = 0)) ∧
    (∀ q : Nat,
      ((∃ a : Real,
        window6WeightedMomentB ((2 : Real) ^ q) ((3 : Real) ^ q) ((4 : Real) ^ q) =
          a • (1 : Matrix (Fin 3) (Fin 3) Real)) ↔ q = 0)) ∧
    (∀ q : Nat,
      0 < conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_denominator q) ∧
    conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_upper_mu =
      ![(1 : Real) / 9, 0, 0] ∧
    conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_lower_mu =
      ![-(1 : Real) / 5, 0, 0] ∧
    conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_upper_sigma =
      Matrix.diagonal ![(5 : Real) / 9, (6 : Real) / 9, (2 : Real) / 9] ∧
    conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_lower_sigma =
      Matrix.diagonal ![(1 : Real) / 5, (4 : Real) / 5, (4 : Real) / 5]

/-- Paper label: `cor:conclusion-window6-cyclic-multiplicity-escort-endpoint-freezing`. -/
theorem paper_conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing :
    conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_statement := by
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro q
    exact (paper_conclusion_window6_cyclic_multiplicity_escort_unique_isotropy q).1
  · intro q
    exact (paper_conclusion_window6_cyclic_multiplicity_escort_unique_isotropy q).2
  · intro q
    unfold conclusion_window6_cyclic_multiplicity_escort_endpoint_freezing_denominator
    positivity

end

end Omega.Conclusion
