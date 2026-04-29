import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete two-point data for the monoidal Boolean character rigidity statement. -/
structure xi_time_part9i_monoidal_rigidity_by_two_points_data where
  transpositionValue : Bool

namespace xi_time_part9i_monoidal_rigidity_by_two_points_data

/-- The nontrivial two-point relabeling. -/
def twoPointTransposition : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

/-- The trivial Boolean character on the two-point symmetric group. -/
def trivialCharacter (_σ : Equiv.Perm (Fin 2)) : Bool :=
  false

/-- The sign Boolean character in the two-point model. -/
def signCharacter (σ : Equiv.Perm (Fin 2)) : Bool :=
  if σ 0 = 0 then false else true

/-- The compatible Boolean character determined by the value on the transposition. -/
def character (D : xi_time_part9i_monoidal_rigidity_by_two_points_data)
    (σ : Equiv.Perm (Fin 2)) : Bool :=
  if σ 0 = 0 then false else D.transpositionValue

/-- The transposition image is exactly the two-point datum. -/
theorem transposition_image_forced
    (D : xi_time_part9i_monoidal_rigidity_by_two_points_data) :
    D.character twoPointTransposition = D.transpositionValue := by
  simp [character, twoPointTransposition]

/-- The character is one of the two monoidal Boolean alternatives on two points. -/
def classifiedByTwoPoints (D : xi_time_part9i_monoidal_rigidity_by_two_points_data) :
    Prop :=
  D.character = trivialCharacter ∨ D.character = signCharacter

end xi_time_part9i_monoidal_rigidity_by_two_points_data

/-- Paper label: `thm:xi-time-part9i-monoidal-rigidity-by-two-points`. -/
theorem paper_xi_time_part9i_monoidal_rigidity_by_two_points
    (D : xi_time_part9i_monoidal_rigidity_by_two_points_data) :
    D.classifiedByTwoPoints := by
  cases hD : D.transpositionValue
  · left
    funext σ
    simp [xi_time_part9i_monoidal_rigidity_by_two_points_data.character,
      xi_time_part9i_monoidal_rigidity_by_two_points_data.trivialCharacter, hD]
  · right
    funext σ
    simp [xi_time_part9i_monoidal_rigidity_by_two_points_data.character,
      xi_time_part9i_monoidal_rigidity_by_two_points_data.signCharacter, hD]

end Omega.Zeta
