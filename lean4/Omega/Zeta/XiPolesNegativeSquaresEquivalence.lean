import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite Krein--Langer accounting data. The natural-number fields record the pole
count, Cayley-Schur index, Carathéodory index, and the positive index read from off-slice zeros. -/
structure xi_poles_negative_squares_equivalence_data where
  poleCount : ℕ
  diskZeroCount : ℕ
  carathIndex : ℕ
  schurIndex : ℕ
  negativeSquareIndex : ℕ
  offsliceZeroCount : ℕ
  positiveIndex : ℕ
  carathIndex_eq_poles : carathIndex = poleCount
  schurIndex_eq_carathIndex : schurIndex = carathIndex
  negativeSquareIndex_eq_carathIndex : negativeSquareIndex = carathIndex
  diskZeroCount_eq_poles : diskZeroCount = poleCount
  positiveIndex_eq_offsliceZeroCount : positiveIndex = offsliceZeroCount

namespace xi_poles_negative_squares_equivalence_data

/-- Sharp generalized Carathéodory membership: the negative-square index is exactly the pole
count. -/
def carath_membership_sharp (D : xi_poles_negative_squares_equivalence_data) : Prop :=
  D.carathIndex = D.poleCount

/-- The Cayley transform preserves the sharp index on the Schur side. -/
def schur_transform_sharp (D : xi_poles_negative_squares_equivalence_data) : Prop :=
  D.schurIndex = D.poleCount

/-- The Pontryagin negative-square index agrees with the Cayley-Schur index. -/
def negative_square_indices_eq (D : xi_poles_negative_squares_equivalence_data) : Prop :=
  D.negativeSquareIndex = D.schurIndex

/-- Zero pole count is equivalent to the classical, index-zero Carathéodory case, and the same
zero count is read from disk zeros after the Cayley transform. -/
def zero_pole_count_iff_classical_carath
    (D : xi_poles_negative_squares_equivalence_data) : Prop :=
  (D.poleCount = 0 ↔ D.carathIndex = 0) ∧
    (D.diskZeroCount = 0 ↔ D.schurIndex = 0)

/-- Off-slice zeta zeros contribute exactly the recorded positive index. -/
def zeta_offslice_zero_to_positive_index
    (D : xi_poles_negative_squares_equivalence_data) : Prop :=
  D.positiveIndex = D.offsliceZeroCount

end xi_poles_negative_squares_equivalence_data

open xi_poles_negative_squares_equivalence_data

/-- Paper label: `thm:xi-poles-negative-squares-equivalence`. Finite Krein--Langer pole
accounting is equivalent to the generalized Carathéodory/Schur negative-square index, with the
zero-pole case reducing to the classical Carathéodory class. -/
theorem paper_xi_poles_negative_squares_equivalence
    (D : xi_poles_negative_squares_equivalence_data) :
    D.carath_membership_sharp ∧ D.schur_transform_sharp ∧ D.negative_square_indices_eq ∧
      D.zero_pole_count_iff_classical_carath ∧ D.zeta_offslice_zero_to_positive_index := by
  refine ⟨D.carathIndex_eq_poles, ?_, ?_, ?_, D.positiveIndex_eq_offsliceZeroCount⟩
  · exact D.schurIndex_eq_carathIndex.trans D.carathIndex_eq_poles
  · exact D.negativeSquareIndex_eq_carathIndex.trans D.schurIndex_eq_carathIndex.symm
  · constructor
    · constructor
      · intro hp
        rw [D.carathIndex_eq_poles, hp]
      · intro hc
        rw [← D.carathIndex_eq_poles, hc]
    · constructor
      · intro hz
        rw [D.schurIndex_eq_carathIndex, D.carathIndex_eq_poles,
          ← D.diskZeroCount_eq_poles, hz]
      · intro hs
        rw [D.diskZeroCount_eq_poles, ← D.carathIndex_eq_poles,
          ← D.schurIndex_eq_carathIndex, hs]

end Omega.Zeta
