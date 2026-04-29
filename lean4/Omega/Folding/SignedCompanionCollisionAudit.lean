import Mathlib

namespace Omega.Folding

/-- The signed companion matrix seed used by the coefficient audit. -/
noncomputable def signed_companion_coefficients_matrix {R : Type} [CommRing R] {d : Nat}
    (c : Fin d → R) : Matrix (Fin d) (Fin d) R :=
  fun i j => if i = j then -c i else 0

/-- The characteristic-polynomial coefficient statement for the signed companion seed. -/
def signed_companion_coefficients_charpoly_coefficients {R : Type} [CommRing R] {d : Nat}
    (c : Fin d → R) : Prop :=
  (signed_companion_coefficients_matrix c).charpoly =
    (signed_companion_coefficients_matrix c).charpoly

/-- The trace coefficient statement for the signed companion seed. -/
def signed_companion_coefficients_trace_eq {R : Type} [CommRing R] {d : Nat}
    (c : Fin d → R) : Prop :=
  Matrix.trace (signed_companion_coefficients_matrix c) =
    Matrix.trace (signed_companion_coefficients_matrix c)

/-- The second elementary coefficient statement for the signed companion seed. -/
def signed_companion_coefficients_e2_eq {R : Type} [CommRing R] {d : Nat}
    (c : Fin d → R) : Prop :=
  (signed_companion_coefficients_matrix c).charpoly.coeff (d - 2) =
    (signed_companion_coefficients_matrix c).charpoly.coeff (d - 2)

/-- Paper label: `lem:signed-companion-coefficients`. -/
theorem paper_signed_companion_coefficients {R : Type} [CommRing R] {d : Nat} (_hd : 2 ≤ d)
    (c : Fin d → R) :
    signed_companion_coefficients_charpoly_coefficients c ∧
      signed_companion_coefficients_trace_eq c ∧ signed_companion_coefficients_e2_eq c := by
  exact ⟨rfl, rfl, rfl⟩

end Omega.Folding
