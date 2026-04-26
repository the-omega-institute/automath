import Mathlib.Tactic

namespace Omega.EA

/-- Binary magma terms in variables indexed by `Fin n`. -/
inductive finite_field_linearization_term (n : Nat) : Type
  | finite_field_linearization_var : Fin n → finite_field_linearization_term n
  | finite_field_linearization_diamond :
      finite_field_linearization_term n →
      finite_field_linearization_term n →
      finite_field_linearization_term n

/-- A small two-parameter polynomial syntax for coefficients in `a` and `b`. -/
inductive finite_field_linearization_poly : Type
  | finite_field_linearization_zero : finite_field_linearization_poly
  | finite_field_linearization_one : finite_field_linearization_poly
  | finite_field_linearization_add :
      finite_field_linearization_poly →
      finite_field_linearization_poly →
      finite_field_linearization_poly
  | finite_field_linearization_mul_a :
      finite_field_linearization_poly → finite_field_linearization_poly
  | finite_field_linearization_mul_b :
      finite_field_linearization_poly → finite_field_linearization_poly

/-- Total-degree upper bound for the coefficient-polynomial syntax. -/
def finite_field_linearization_poly_degree : finite_field_linearization_poly → Nat
  | .finite_field_linearization_zero => 0
  | .finite_field_linearization_one => 0
  | .finite_field_linearization_add p q =>
      max (finite_field_linearization_poly_degree p) (finite_field_linearization_poly_degree q)
  | .finite_field_linearization_mul_a p => finite_field_linearization_poly_degree p + 1
  | .finite_field_linearization_mul_b p => finite_field_linearization_poly_degree p + 1

/-- Number of internal binary-operation nodes of a term. -/
def finite_field_linearization_internal_nodes {n : Nat} :
    finite_field_linearization_term n → Nat
  | .finite_field_linearization_var _ => 0
  | .finite_field_linearization_diamond u v =>
      finite_field_linearization_internal_nodes u + finite_field_linearization_internal_nodes v + 1

/-- Recursive coefficient of variable `x_i` under the interpretation `x ⋄ y = a x + b y`. -/
def finite_field_linearization_coeff {n : Nat}
    (t : finite_field_linearization_term n) (i : Fin n) :
    finite_field_linearization_poly :=
  match t with
  | .finite_field_linearization_var j =>
      if i = j then
        .finite_field_linearization_one
      else
        .finite_field_linearization_zero
  | .finite_field_linearization_diamond u v =>
      .finite_field_linearization_add
        (.finite_field_linearization_mul_a (finite_field_linearization_coeff u i))
        (.finite_field_linearization_mul_b (finite_field_linearization_coeff v i))

/-- The coefficient polynomials of a linearized magma term have degree bounded by its size. -/
def finite_field_linearization_statement
    (n : Nat) (t : finite_field_linearization_term n) : Prop :=
  ∀ i : Fin n,
    finite_field_linearization_poly_degree (finite_field_linearization_coeff t i) ≤
      finite_field_linearization_internal_nodes t

/-- Paper label: `thm:finite-field-linearization`. -/
theorem paper_finite_field_linearization
    (n : Nat) (t : finite_field_linearization_term n) :
    finite_field_linearization_statement n t := by
  intro i
  induction t with
  | finite_field_linearization_var j =>
      by_cases h : i = j <;>
        simp [finite_field_linearization_coeff,
          finite_field_linearization_internal_nodes, finite_field_linearization_poly_degree, h]
  | finite_field_linearization_diamond u v ihu ihv =>
      simp [finite_field_linearization_coeff,
        finite_field_linearization_internal_nodes, finite_field_linearization_poly_degree]
      omega

end Omega.EA
