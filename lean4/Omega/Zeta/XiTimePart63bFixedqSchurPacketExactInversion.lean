import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite character packet used for the exact fixed-`q` Schur inversion formula. -/
structure xi_time_part63b_fixedq_schur_packet_exact_inversion_data where
  q : ℕ
  schur_character : Fin q → Fin q → ℚ
  schur_dimension : Fin q → ℚ
  cycle_weight : Fin q → ℚ
  schur_coordinate : Fin q → ℚ
  collision_coordinate : Fin q → ℚ
  schur_dimension_ne_zero : ∀ lam, schur_dimension lam ≠ 0
  cycle_weight_ne_zero : ∀ mu, cycle_weight mu ≠ 0
  forward_tomography :
    ∀ lam,
      schur_coordinate lam / schur_dimension lam =
        ∑ mu, schur_character lam mu / cycle_weight mu * collision_coordinate mu
  column_orthogonality :
    ∀ mu nu,
      ∑ lam, schur_character lam mu * schur_character lam nu =
        if mu = nu then cycle_weight mu else 0
  row_orthogonality :
    ∀ lam nu,
      ∑ mu, schur_character lam mu * schur_character nu mu / cycle_weight mu =
        if lam = nu then 1 else 0

/-- Forward Schur packet map. -/
def xi_time_part63b_fixedq_schur_packet_exact_inversion_forward_map
    (D : xi_time_part63b_fixedq_schur_packet_exact_inversion_data) (x : Fin D.q → ℚ) :
    Fin D.q → ℚ :=
  fun lam => D.schur_dimension lam * ∑ mu, D.schur_character lam mu / D.cycle_weight mu * x mu

/-- Inverse character-summation map. -/
def xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map
    (D : xi_time_part63b_fixedq_schur_packet_exact_inversion_data) (y : Fin D.q → ℚ) :
    Fin D.q → ℚ :=
  fun mu => ∑ lam, D.schur_character lam mu / D.schur_dimension lam * y lam

namespace xi_time_part63b_fixedq_schur_packet_exact_inversion_data

/-- Paper-facing statement: the inverse character sum exactly recovers the collision coordinates,
and the explicit forward and inverse coordinate transforms are mutual inverses. -/
def statement (D : xi_time_part63b_fixedq_schur_packet_exact_inversion_data) : Prop :=
  (∀ mu,
    xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map D D.schur_coordinate mu =
      D.collision_coordinate mu) ∧
    Function.LeftInverse
      (xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map D)
      (xi_time_part63b_fixedq_schur_packet_exact_inversion_forward_map D) ∧
    Function.RightInverse
      (xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map D)
      (xi_time_part63b_fixedq_schur_packet_exact_inversion_forward_map D)

end xi_time_part63b_fixedq_schur_packet_exact_inversion_data

open xi_time_part63b_fixedq_schur_packet_exact_inversion_data

private lemma xi_time_part63b_fixedq_schur_packet_exact_inversion_left_inverse
    (D : xi_time_part63b_fixedq_schur_packet_exact_inversion_data) :
    Function.LeftInverse
      (xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map D)
      (xi_time_part63b_fixedq_schur_packet_exact_inversion_forward_map D) := by
  intro x
  funext mu
  unfold xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map
    xi_time_part63b_fixedq_schur_packet_exact_inversion_forward_map
  calc
    ∑ lam, D.schur_character lam mu / D.schur_dimension lam *
        (D.schur_dimension lam * ∑ nu, D.schur_character lam nu / D.cycle_weight nu * x nu)
        = ∑ lam, D.schur_character lam mu * ∑ nu,
            D.schur_character lam nu / D.cycle_weight nu * x nu := by
            refine Finset.sum_congr rfl ?_
            intro lam hlam
            field_simp [D.schur_dimension_ne_zero lam]
    _ = ∑ lam, ∑ nu, D.schur_character lam mu *
          (D.schur_character lam nu / D.cycle_weight nu * x nu) := by
          refine Finset.sum_congr rfl ?_
          intro lam hlam
          rw [Finset.mul_sum]
    _ = ∑ nu, ∑ lam, D.schur_character lam mu *
          (D.schur_character lam nu / D.cycle_weight nu * x nu) := by
          rw [Finset.sum_comm]
    _ = ∑ nu, ((∑ lam, D.schur_character lam mu *
          (D.schur_character lam nu / D.cycle_weight nu)) * x nu) := by
          refine Finset.sum_congr rfl ?_
          intro nu hnu
          calc
            ∑ lam, D.schur_character lam mu * (D.schur_character lam nu / D.cycle_weight nu * x nu)
                = ∑ lam, (D.schur_character lam mu *
                    (D.schur_character lam nu / D.cycle_weight nu)) * x nu := by
                    refine Finset.sum_congr rfl ?_
                    intro lam hlam
                    ring
            _ = (∑ lam, D.schur_character lam mu *
                    (D.schur_character lam nu / D.cycle_weight nu)) * x nu := by
                  rw [Finset.sum_mul]
    _ = ∑ nu, (((∑ lam, D.schur_character lam mu * D.schur_character lam nu) /
          D.cycle_weight nu) * x nu) := by
          refine Finset.sum_congr rfl ?_
          intro nu hnu
          congr 1
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro lam hlam
          field_simp [D.cycle_weight_ne_zero nu]
    _ = ∑ nu, (((if mu = nu then D.cycle_weight mu else 0) / D.cycle_weight nu) * x nu) := by
          refine Finset.sum_congr rfl ?_
          intro nu hnu
          rw [D.column_orthogonality mu nu]
    _ = x mu := by
          classical
          have hrewrite :
              ∑ nu, (((if mu = nu then D.cycle_weight mu else 0) / D.cycle_weight nu) * x nu) =
                ∑ nu, if mu = nu then x nu else 0 := by
            refine Finset.sum_congr rfl ?_
            intro nu hnu
            by_cases hEq : mu = nu
            · subst hEq
              simp [D.cycle_weight_ne_zero mu]
            · simp [hEq, D.cycle_weight_ne_zero nu]
          rw [hrewrite]
          simp

private lemma xi_time_part63b_fixedq_schur_packet_exact_inversion_right_inverse
    (D : xi_time_part63b_fixedq_schur_packet_exact_inversion_data) :
    Function.RightInverse
      (xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map D)
      (xi_time_part63b_fixedq_schur_packet_exact_inversion_forward_map D) := by
  intro y
  funext lam
  unfold xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map
    xi_time_part63b_fixedq_schur_packet_exact_inversion_forward_map
  calc
    D.schur_dimension lam * ∑ mu, D.schur_character lam mu / D.cycle_weight mu *
        (∑ nu, D.schur_character nu mu / D.schur_dimension nu * y nu)
        = D.schur_dimension lam * ∑ mu, ∑ nu,
            D.schur_character lam mu / D.cycle_weight mu *
              (D.schur_character nu mu / D.schur_dimension nu * y nu) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro mu hmu
            rw [Finset.mul_sum]
    _ = D.schur_dimension lam * ∑ nu, ∑ mu,
          D.schur_character lam mu / D.cycle_weight mu *
            (D.schur_character nu mu / D.schur_dimension nu * y nu) := by
          rw [Finset.sum_comm]
    _ = D.schur_dimension lam * ∑ nu,
          ((∑ mu, D.schur_character lam mu / D.cycle_weight mu *
            (D.schur_character nu mu / D.schur_dimension nu)) * y nu) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro nu hnu
          calc
            ∑ mu, D.schur_character lam mu / D.cycle_weight mu *
                (D.schur_character nu mu / D.schur_dimension nu * y nu)
                = ∑ mu, (D.schur_character lam mu / D.cycle_weight mu *
                    (D.schur_character nu mu / D.schur_dimension nu)) * y nu := by
                    refine Finset.sum_congr rfl ?_
                    intro mu hmu
                    ring
            _ = (∑ mu, D.schur_character lam mu / D.cycle_weight mu *
                    (D.schur_character nu mu / D.schur_dimension nu)) * y nu := by
                  rw [Finset.sum_mul]
    _ = D.schur_dimension lam * ∑ nu,
          (((∑ mu, D.schur_character lam mu * D.schur_character nu mu / D.cycle_weight mu) /
            D.schur_dimension nu) * y nu) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro nu hnu
          congr 1
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro mu hmu
          field_simp [D.schur_dimension_ne_zero nu, D.cycle_weight_ne_zero mu]
    _ = D.schur_dimension lam * ∑ nu,
          (((if lam = nu then 1 else 0) / D.schur_dimension nu) * y nu) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro nu hnu
          rw [D.row_orthogonality lam nu]
    _ = y lam := by
          classical
          have hsum :
              ∑ nu, (((if lam = nu then 1 else 0) / D.schur_dimension nu) * y nu) =
                (1 / D.schur_dimension lam) * y lam := by
            have hrewrite :
                ∑ nu, (((if lam = nu then 1 else 0) / D.schur_dimension nu) * y nu) =
                  ∑ nu, if lam = nu then (1 / D.schur_dimension nu) * y nu else 0 := by
              refine Finset.sum_congr rfl ?_
              intro nu hnu
              by_cases hEq : lam = nu
              · simp [hEq]
              · simp [hEq]
            rw [hrewrite]
            simp [D.schur_dimension_ne_zero]
          rw [hsum]
          field_simp [D.schur_dimension_ne_zero lam]

/-- Exact inversion of the fixed-`q` Schur packet.
    thm:xi-time-part63b-fixedq-schur-packet-exact-inversion -/
theorem paper_xi_time_part63b_fixedq_schur_packet_exact_inversion
    (D : xi_time_part63b_fixedq_schur_packet_exact_inversion_data) : D.statement := by
  refine ⟨?_, xi_time_part63b_fixedq_schur_packet_exact_inversion_left_inverse D,
    xi_time_part63b_fixedq_schur_packet_exact_inversion_right_inverse D⟩
  intro mu
  have hleft := xi_time_part63b_fixedq_schur_packet_exact_inversion_left_inverse D
  have hforward :
      xi_time_part63b_fixedq_schur_packet_exact_inversion_forward_map D D.collision_coordinate =
        D.schur_coordinate := by
    funext lam
    unfold xi_time_part63b_fixedq_schur_packet_exact_inversion_forward_map
    rw [← D.forward_tomography lam]
    field_simp [D.schur_dimension_ne_zero lam]
  rw [← hforward]
  exact congrFun (hleft D.collision_coordinate) mu

end Omega.Zeta
