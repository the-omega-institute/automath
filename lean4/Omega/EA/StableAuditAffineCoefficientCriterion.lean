import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.EA

/-- Six-variable magma terms used by the affine coefficient audit. -/
inductive stable_audit_affine_coefficient_criterion_term where
  | var : Fin 6 → stable_audit_affine_coefficient_criterion_term
  | op :
      stable_audit_affine_coefficient_criterion_term →
      stable_audit_affine_coefficient_criterion_term →
      stable_audit_affine_coefficient_criterion_term
deriving DecidableEq, Repr

/-- Concrete coefficient data for the affine magma operation `x ⋄ y = a*x + b*y` on `ZMod n`. -/
structure stable_audit_affine_coefficient_criterion_data where
  n : ℕ
  a : ZMod n
  b : ZMod n

namespace stable_audit_affine_coefficient_criterion_data

open stable_audit_affine_coefficient_criterion_term

/-- Evaluation of a magma term under the affine operation `x ⋄ y = a*x + b*y`. -/
def stable_audit_affine_coefficient_criterion_eval
    (D : stable_audit_affine_coefficient_criterion_data) (ρ : Fin 6 → ZMod D.n) :
    stable_audit_affine_coefficient_criterion_term → ZMod D.n
  | var i => ρ i
  | op s t =>
      D.a * D.stable_audit_affine_coefficient_criterion_eval ρ s +
        D.b * D.stable_audit_affine_coefficient_criterion_eval ρ t

/-- The coefficient vector of a term in the affine magma. -/
def stable_audit_affine_coefficient_criterion_coeff
    (D : stable_audit_affine_coefficient_criterion_data) :
    stable_audit_affine_coefficient_criterion_term → Fin 6 → ZMod D.n
  | var i, j => if j = i then 1 else 0
  | op s t, j =>
      D.a * D.stable_audit_affine_coefficient_criterion_coeff s j +
        D.b * D.stable_audit_affine_coefficient_criterion_coeff t j

/-- Dot product of a coefficient vector with a variable assignment. -/
def stable_audit_affine_coefficient_criterion_dot
    (D : stable_audit_affine_coefficient_criterion_data)
    (c : Fin 6 → ZMod D.n) (ρ : Fin 6 → ZMod D.n) : ZMod D.n :=
  ∑ i : Fin 6, c i * ρ i

lemma stable_audit_affine_coefficient_criterion_eval_eq_dot
    (D : stable_audit_affine_coefficient_criterion_data) (ρ : Fin 6 → ZMod D.n) :
    ∀ t,
      D.stable_audit_affine_coefficient_criterion_eval ρ t =
        D.stable_audit_affine_coefficient_criterion_dot
          (D.stable_audit_affine_coefficient_criterion_coeff t) ρ
  | var i => by
      simp [stable_audit_affine_coefficient_criterion_eval,
        stable_audit_affine_coefficient_criterion_coeff,
        stable_audit_affine_coefficient_criterion_dot]
  | op s t => by
      rw [stable_audit_affine_coefficient_criterion_eval,
        stable_audit_affine_coefficient_criterion_eval_eq_dot D ρ s,
        stable_audit_affine_coefficient_criterion_eval_eq_dot D ρ t]
      simp [stable_audit_affine_coefficient_criterion_coeff,
        stable_audit_affine_coefficient_criterion_dot, Finset.sum_add_distrib, Finset.mul_sum,
        mul_add, mul_left_comm, mul_comm]

lemma stable_audit_affine_coefficient_criterion_dot_basis
    (D : stable_audit_affine_coefficient_criterion_data) (c : Fin 6 → ZMod D.n)
    (i : Fin 6) :
    D.stable_audit_affine_coefficient_criterion_dot c
        (fun j => if j = i then 1 else 0) = c i := by
  simp [stable_audit_affine_coefficient_criterion_dot]

end stable_audit_affine_coefficient_criterion_data

open stable_audit_affine_coefficient_criterion_data

/-- The paper-facing affine coefficient criterion: two affine magma terms agree under every
assignment over `ZMod n` iff their recursively computed coefficient vectors agree. -/
def stable_audit_affine_coefficient_criterion_statement
    (D : stable_audit_affine_coefficient_criterion_data) : Prop :=
  ∀ s t : stable_audit_affine_coefficient_criterion_term,
    (∀ ρ : Fin 6 → ZMod D.n,
      D.stable_audit_affine_coefficient_criterion_eval ρ s =
        D.stable_audit_affine_coefficient_criterion_eval ρ t) ↔
      D.stable_audit_affine_coefficient_criterion_coeff s =
        D.stable_audit_affine_coefficient_criterion_coeff t

/-- Paper label: `lem:stable-audit-affine-coefficient-criterion`. -/
theorem paper_stable_audit_affine_coefficient_criterion
    (D : stable_audit_affine_coefficient_criterion_data) :
    stable_audit_affine_coefficient_criterion_statement D := by
  intro s t
  constructor
  · intro h
    funext i
    have hbasis := h (fun j => if j = i then 1 else 0)
    rw [D.stable_audit_affine_coefficient_criterion_eval_eq_dot,
      D.stable_audit_affine_coefficient_criterion_eval_eq_dot,
      D.stable_audit_affine_coefficient_criterion_dot_basis,
      D.stable_audit_affine_coefficient_criterion_dot_basis] at hbasis
    exact hbasis
  · intro h ρ
    rw [D.stable_audit_affine_coefficient_criterion_eval_eq_dot,
      D.stable_audit_affine_coefficient_criterion_eval_eq_dot, h]

end Omega.EA
