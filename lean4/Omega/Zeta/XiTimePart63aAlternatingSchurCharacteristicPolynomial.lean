import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

/-- Positive rational fiber multiplicity attached to a natural datum. -/
def xi_time_part63a_alternating_schur_characteristic_polynomial_weight (n : Nat) : ℚ :=
  n + 1

/-- The finite product form of the alternating Schur characteristic polynomial. -/
noncomputable def xi_time_part63a_alternating_schur_characteristic_polynomial_product :
    List Nat → Polynomial ℚ
  | [] => 1
  | n :: d =>
      (1 +
          C (xi_time_part63a_alternating_schur_characteristic_polynomial_weight n) * X) *
        xi_time_part63a_alternating_schur_characteristic_polynomial_product d

/-- The coefficient sequence of the finite alternating Schur product. -/
noncomputable def xi_time_part63a_alternating_schur_characteristic_polynomial_coeff
    (d : List Nat) (q : Nat) : ℚ :=
  (xi_time_part63a_alternating_schur_characteristic_polynomial_product d).coeff q

/-- The advertised finite coefficient packet, cut off after the product length. -/
noncomputable def xi_time_part63a_alternating_schur_characteristic_polynomial_finite_coeff
    (d : List Nat) (q : Nat) : ℚ :=
  if q ≤ d.length then
    xi_time_part63a_alternating_schur_characteristic_polynomial_coeff d q
  else
    0

lemma xi_time_part63a_alternating_schur_characteristic_polynomial_eval_product
    (d : List Nat) (z : ℚ) :
    (xi_time_part63a_alternating_schur_characteristic_polynomial_product d).eval z =
      (d.map fun n =>
        1 + xi_time_part63a_alternating_schur_characteristic_polynomial_weight n * z).prod := by
  induction d with
  | nil =>
      simp [xi_time_part63a_alternating_schur_characteristic_polynomial_product]
  | cons n d ih =>
      simp [xi_time_part63a_alternating_schur_characteristic_polynomial_product, ih,
        xi_time_part63a_alternating_schur_characteristic_polynomial_weight, mul_comm]

lemma xi_time_part63a_alternating_schur_characteristic_polynomial_root_of_mem
    {d : List Nat} {n : Nat} (hn : n ∈ d) :
    (xi_time_part63a_alternating_schur_characteristic_polynomial_product d).eval
        (-(xi_time_part63a_alternating_schur_characteristic_polynomial_weight n)⁻¹) = 0 := by
  induction d with
  | nil =>
      simp at hn
  | cons m d ih =>
      rcases List.mem_cons.mp hn with hnm | hn
      · subst n
        set w := xi_time_part63a_alternating_schur_characteristic_polynomial_weight m
        have hw : w ≠ 0 := by
          have hpos : 0 < w := by
            subst w
            dsimp [xi_time_part63a_alternating_schur_characteristic_polynomial_weight]
            positivity
          exact ne_of_gt hpos
        have hfactor : (1 : ℚ) + w * (-w⁻¹) = 0 := by
          field_simp [hw]
          ring
        change
          ((1 + C w * X) *
              xi_time_part63a_alternating_schur_characteristic_polynomial_product d).eval
            (-w⁻¹) = 0
        rw [eval_mul]
        have hf : (1 + C w * X).eval (-w⁻¹) = 0 := by
          simpa using hfactor
        simp [hf]
      · simp [xi_time_part63a_alternating_schur_characteristic_polynomial_product, ih hn]

/-- Concrete finite-list package for the alternating Schur characteristic polynomial. -/
def xi_time_part63a_alternating_schur_characteristic_polynomial_statement
    (d : List Nat) : Prop :=
  (∀ z : ℚ,
    (xi_time_part63a_alternating_schur_characteristic_polynomial_product d).eval z =
      (d.map fun n =>
        1 + xi_time_part63a_alternating_schur_characteristic_polynomial_weight n * z).prod) ∧
    (∀ q, d.length < q →
      xi_time_part63a_alternating_schur_characteristic_polynomial_finite_coeff d q = 0) ∧
      (∀ n ∈ d,
        (xi_time_part63a_alternating_schur_characteristic_polynomial_product d).eval
          (-(xi_time_part63a_alternating_schur_characteristic_polynomial_weight n)⁻¹) = 0) ∧
        (∀ P : Polynomial ℚ,
          P = xi_time_part63a_alternating_schur_characteristic_polynomial_product d ↔
            ∀ q,
              P.coeff q =
                xi_time_part63a_alternating_schur_characteristic_polynomial_coeff d q)

/-- Paper label:
`thm:xi-time-part63a-alternating-schur-characteristic-polynomial`. -/
theorem paper_xi_time_part63a_alternating_schur_characteristic_polynomial (d : List Nat) :
    xi_time_part63a_alternating_schur_characteristic_polynomial_statement d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact xi_time_part63a_alternating_schur_characteristic_polynomial_eval_product d
  · intro q hq
    simp [xi_time_part63a_alternating_schur_characteristic_polynomial_finite_coeff,
      Nat.not_le_of_gt hq]
  · intro n hn
    exact xi_time_part63a_alternating_schur_characteristic_polynomial_root_of_mem hn
  · intro P
    constructor
    · intro h q
      simp [h, xi_time_part63a_alternating_schur_characteristic_polynomial_coeff]
    · intro h
      ext q
      simpa [xi_time_part63a_alternating_schur_characteristic_polynomial_coeff] using h q

end Omega.Zeta
