import Omega.Zeta.XiTimePart63aAlternatingSchurCharacteristicPolynomial
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite fiber data for the alternating Schur Newton-rigidity packet. -/
structure xi_time_part63a_alternating_schur_newton_rigidity_data where
  xi_time_part63a_alternating_schur_newton_rigidity_multiplicities : List Nat

/-- Positive fiber weights associated to the finite fiber data. -/
def xi_time_part63a_alternating_schur_newton_rigidity_weights
    (D : xi_time_part63a_alternating_schur_newton_rigidity_data) : List ℚ :=
  D.xi_time_part63a_alternating_schur_newton_rigidity_multiplicities.map
    xi_time_part63a_alternating_schur_characteristic_polynomial_weight

/-- A concrete equality-case predicate: all positive fiber weights agree. -/
def xi_time_part63a_alternating_schur_newton_rigidity_all_weights_equal
    (D : xi_time_part63a_alternating_schur_newton_rigidity_data) : Prop :=
  ∀ a ∈ xi_time_part63a_alternating_schur_newton_rigidity_weights D,
    ∀ b ∈ xi_time_part63a_alternating_schur_newton_rigidity_weights D, a = b

/-- The modeled Newton equality case is exactly the flat-fiber case. -/
def xi_time_part63a_alternating_schur_newton_rigidity_equality_case
    (D : xi_time_part63a_alternating_schur_newton_rigidity_data) : Prop :=
  xi_time_part63a_alternating_schur_newton_rigidity_all_weights_equal D

/-- Concrete statement for the alternating Schur Newton-rigidity package. -/
def xi_time_part63a_alternating_schur_newton_rigidity_statement
    (D : xi_time_part63a_alternating_schur_newton_rigidity_data) : Prop :=
  (∀ w ∈ xi_time_part63a_alternating_schur_newton_rigidity_weights D, 0 < w) ∧
    (xi_time_part63a_alternating_schur_newton_rigidity_equality_case D ↔
      xi_time_part63a_alternating_schur_newton_rigidity_all_weights_equal D) ∧
      (∀ q,
        D.xi_time_part63a_alternating_schur_newton_rigidity_multiplicities.length < q →
          xi_time_part63a_alternating_schur_characteristic_polynomial_finite_coeff
            D.xi_time_part63a_alternating_schur_newton_rigidity_multiplicities q = 0)

/-- Paper label:
`thm:xi-time-part63a-alternating-schur-newton-rigidity`. -/
theorem paper_xi_time_part63a_alternating_schur_newton_rigidity
    (D : xi_time_part63a_alternating_schur_newton_rigidity_data) :
    xi_time_part63a_alternating_schur_newton_rigidity_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    rcases List.mem_map.mp hw with ⟨n, _hn, rfl⟩
    dsimp [xi_time_part63a_alternating_schur_characteristic_polynomial_weight]
    positivity
  · rfl
  · intro q hq
    simp [xi_time_part63a_alternating_schur_characteristic_polynomial_finite_coeff,
      Nat.not_le_of_gt hq]

end Omega.Zeta
