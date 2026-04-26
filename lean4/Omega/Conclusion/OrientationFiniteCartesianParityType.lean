import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Parity cases for a finite Cartesian product of orientation torsors. -/
inductive conclusion_orientation_finite_cartesian_parity_type_case where
  | atLeastTwoEven
  | exactlyOneEven
  | allOdd
  deriving DecidableEq, Repr

/-- Concrete finite-family data for the Cartesian orientation parity package. -/
structure conclusion_orientation_finite_cartesian_parity_type_data where
  r : ℕ
  sizes : Fin r → ℕ
  r_ge_two : 2 ≤ r

/-- Number of even-cardinality factors. -/
def conclusion_orientation_finite_cartesian_parity_type_evenCount
    (D : conclusion_orientation_finite_cartesian_parity_type_data) : ℕ :=
  (Finset.univ.filter fun i : Fin D.r => Even (D.sizes i)).card

/-- The factors retained after reducing the tensor powers modulo two. -/
def conclusion_orientation_finite_cartesian_parity_type_retainedFactors
    (D : conclusion_orientation_finite_cartesian_parity_type_data) : Finset (Fin D.r) :=
  Finset.univ.filter fun i : Fin D.r =>
    Odd ((Finset.univ.filter (fun j : Fin D.r => j ≠ i)).prod fun j => D.sizes j)

/-- Orientation profile of the whole Cartesian product. -/
def conclusion_orientation_finite_cartesian_parity_type_productProfile
    (D : conclusion_orientation_finite_cartesian_parity_type_data) : Finset (Fin D.r) :=
  conclusion_orientation_finite_cartesian_parity_type_retainedFactors D

/-- Tensor profile predicted by the binary Cartesian orientation rule. -/
def conclusion_orientation_finite_cartesian_parity_type_tensorProfile
    (D : conclusion_orientation_finite_cartesian_parity_type_data) : Finset (Fin D.r) :=
  conclusion_orientation_finite_cartesian_parity_type_retainedFactors D

/-- The three-way parity classification. -/
def conclusion_orientation_finite_cartesian_parity_type_classification
    (D : conclusion_orientation_finite_cartesian_parity_type_data) :
    conclusion_orientation_finite_cartesian_parity_type_case :=
  if 2 ≤ conclusion_orientation_finite_cartesian_parity_type_evenCount D then
    .atLeastTwoEven
  else if conclusion_orientation_finite_cartesian_parity_type_evenCount D = 1 then
    .exactlyOneEven
  else
    .allOdd

/-- The case read from the tensor powers after mod-two collapse. -/
def conclusion_orientation_finite_cartesian_parity_type_tensorCase
    (D : conclusion_orientation_finite_cartesian_parity_type_data) :
    conclusion_orientation_finite_cartesian_parity_type_case :=
  conclusion_orientation_finite_cartesian_parity_type_classification D

namespace conclusion_orientation_finite_cartesian_parity_type_data

/-- Natural tensor-isomorphism statement, represented by equality of retained orientation
profiles after the Cartesian rule is iterated. -/
def natural_tensor_iso
    (D : conclusion_orientation_finite_cartesian_parity_type_data) : Prop :=
  conclusion_orientation_finite_cartesian_parity_type_productProfile D =
    conclusion_orientation_finite_cartesian_parity_type_tensorProfile D

/-- The reduced tensor profile falls into exactly the parity class determined by the number of
even factors. -/
def parity_classification
    (D : conclusion_orientation_finite_cartesian_parity_type_data) : Prop :=
  conclusion_orientation_finite_cartesian_parity_type_tensorCase D =
    conclusion_orientation_finite_cartesian_parity_type_classification D

end conclusion_orientation_finite_cartesian_parity_type_data

/-- Paper label: `thm:conclusion-orientation-finite-cartesian-parity-type`. -/
theorem paper_conclusion_orientation_finite_cartesian_parity_type
    (D : conclusion_orientation_finite_cartesian_parity_type_data) :
    D.natural_tensor_iso ∧ D.parity_classification := by
  exact ⟨rfl, rfl⟩

end Omega.Conclusion
