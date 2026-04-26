import Mathlib.Tactic

namespace Omega.EA

/-- Binary magma terms for the window-`6` first/last classifier. -/
inductive window6_first_last_classifier_term (n : Nat) : Type
  | window6_first_last_classifier_var : Fin n → window6_first_last_classifier_term n
  | window6_first_last_classifier_op :
      window6_first_last_classifier_term n →
      window6_first_last_classifier_term n →
      window6_first_last_classifier_term n

/-- The first variable occurring in a binary magma term. -/
def window6_first_last_classifier_first {n : Nat} :
    window6_first_last_classifier_term n → Fin n
  | .window6_first_last_classifier_var i => i
  | .window6_first_last_classifier_op u _ => window6_first_last_classifier_first u

/-- The last variable occurring in a binary magma term. -/
def window6_first_last_classifier_last {n : Nat} :
    window6_first_last_classifier_term n → Fin n
  | .window6_first_last_classifier_var i => i
  | .window6_first_last_classifier_op _ v => window6_first_last_classifier_last v

/-- Evaluation in CRT coordinates for the rectangular-band window-`6` operation. -/
def window6_first_last_classifier_eval {n : Nat}
    (ρ3 : Fin n → Nat) (ρ7 : Fin n → Nat) :
    window6_first_last_classifier_term n → Nat × Nat
  | .window6_first_last_classifier_var i => (ρ3 i % 3, ρ7 i % 7)
  | .window6_first_last_classifier_op u v =>
      ((window6_first_last_classifier_eval ρ3 ρ7 u).1,
        (window6_first_last_classifier_eval ρ3 ρ7 v).2)

/-- The CRT rectangular-band evaluation of a binary magma term is determined by its first
mod-`3` coordinate and last mod-`7` coordinate.
    lem:window6-first-last-classifier -/
theorem paper_window6_first_last_classifier {n : Nat}
    (t : window6_first_last_classifier_term n) (ρ3 : Fin n → Nat) (ρ7 : Fin n → Nat) :
    window6_first_last_classifier_eval ρ3 ρ7 t =
      (ρ3 (window6_first_last_classifier_first t) % 3,
        ρ7 (window6_first_last_classifier_last t) % 7) := by
  induction t with
  | window6_first_last_classifier_var i =>
      rfl
  | window6_first_last_classifier_op u v hu hv =>
      simp [window6_first_last_classifier_eval, window6_first_last_classifier_first,
        window6_first_last_classifier_last, hu, hv]

/-- Terms in the four variables used by the ETP order-four certificate entries. -/
abbrev window6_fin21_facts_certificate_term :=
  window6_first_last_classifier_term 4

/-- A variable term for the window-`6` finite certificate encoding. -/
def window6_fin21_facts_certificate_var (i : Fin 4) :
    window6_fin21_facts_certificate_term :=
  .window6_first_last_classifier_var i

/-- A binary operation term for the window-`6` finite certificate encoding. -/
def window6_fin21_facts_certificate_op
    (u v : window6_fin21_facts_certificate_term) :
    window6_fin21_facts_certificate_term :=
  .window6_first_last_classifier_op u v

def window6_fin21_facts_certificate_x : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_var 0

def window6_fin21_facts_certificate_y : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_var 1

def window6_fin21_facts_certificate_z : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_var 2

def window6_fin21_facts_certificate_w : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_var 3

/-- In the rectangular-band classifier, an equation holds exactly when first and last variables
match. -/
def window6_fin21_facts_certificate_equation_holds
    (s t : window6_fin21_facts_certificate_term) : Prop :=
  window6_first_last_classifier_first s = window6_first_last_classifier_first t ∧
    window6_first_last_classifier_last s = window6_first_last_classifier_last t

/-- ETP index `10`: `x = x <> (y <> x)`. -/
def window6_fin21_facts_certificate_e10_lhs : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_x

def window6_fin21_facts_certificate_e10_rhs : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_op window6_fin21_facts_certificate_x
    (window6_fin21_facts_certificate_op window6_fin21_facts_certificate_y
      window6_fin21_facts_certificate_x)

/-- ETP index `43`: `x <> y = y <> x`. -/
def window6_fin21_facts_certificate_e43_lhs : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_op window6_fin21_facts_certificate_x
    window6_fin21_facts_certificate_y

def window6_fin21_facts_certificate_e43_rhs : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_op window6_fin21_facts_certificate_y
    window6_fin21_facts_certificate_x

/-- ETP index `46`: `x <> y = z <> w`. -/
def window6_fin21_facts_certificate_e46_lhs : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_op window6_fin21_facts_certificate_x
    window6_fin21_facts_certificate_y

def window6_fin21_facts_certificate_e46_rhs : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_op window6_fin21_facts_certificate_z
    window6_fin21_facts_certificate_w

/-- ETP index `52`: `x = x <> (y <> (x <> x))`. -/
def window6_fin21_facts_certificate_e52_lhs : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_x

def window6_fin21_facts_certificate_e52_rhs : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_op window6_fin21_facts_certificate_x
    (window6_fin21_facts_certificate_op window6_fin21_facts_certificate_y
      (window6_fin21_facts_certificate_op window6_fin21_facts_certificate_x
        window6_fin21_facts_certificate_x))

/-- ETP index `55`: `x = x <> (y <> (y <> x))`. -/
def window6_fin21_facts_certificate_e55_lhs : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_x

def window6_fin21_facts_certificate_e55_rhs : window6_fin21_facts_certificate_term :=
  window6_fin21_facts_certificate_op window6_fin21_facts_certificate_x
    (window6_fin21_facts_certificate_op window6_fin21_facts_certificate_y
      (window6_fin21_facts_certificate_op window6_fin21_facts_certificate_y
        window6_fin21_facts_certificate_x))

/-- The classifier-level form of `Facts G [10, 52, 55] [43, 46]` for the window-`6`,
`Fin 21` rectangular-band model. -/
def window6_fin21_facts_certificate_statement : Prop :=
  window6_fin21_facts_certificate_equation_holds
      window6_fin21_facts_certificate_e10_lhs window6_fin21_facts_certificate_e10_rhs ∧
    window6_fin21_facts_certificate_equation_holds
      window6_fin21_facts_certificate_e52_lhs window6_fin21_facts_certificate_e52_rhs ∧
    window6_fin21_facts_certificate_equation_holds
      window6_fin21_facts_certificate_e55_lhs window6_fin21_facts_certificate_e55_rhs ∧
    ¬ window6_fin21_facts_certificate_equation_holds
      window6_fin21_facts_certificate_e43_lhs window6_fin21_facts_certificate_e43_rhs ∧
    ¬ window6_fin21_facts_certificate_equation_holds
      window6_fin21_facts_certificate_e46_lhs window6_fin21_facts_certificate_e46_rhs

/-- The window-`6` `Fin 21` certificate satisfies ETP indices `10`, `52`, and `55`, and
refutes indices `43` and `46`.
    thm:window6-fin21-facts-certificate -/
theorem paper_window6_fin21_facts_certificate :
    window6_fin21_facts_certificate_statement := by
  simp [window6_fin21_facts_certificate_statement,
    window6_fin21_facts_certificate_equation_holds,
    window6_fin21_facts_certificate_e10_lhs, window6_fin21_facts_certificate_e10_rhs,
    window6_fin21_facts_certificate_e43_lhs, window6_fin21_facts_certificate_e43_rhs,
    window6_fin21_facts_certificate_e46_lhs, window6_fin21_facts_certificate_e46_rhs,
    window6_fin21_facts_certificate_e52_lhs, window6_fin21_facts_certificate_e52_rhs,
    window6_fin21_facts_certificate_e55_lhs, window6_fin21_facts_certificate_e55_rhs,
    window6_fin21_facts_certificate_x, window6_fin21_facts_certificate_y,
    window6_fin21_facts_certificate_z, window6_fin21_facts_certificate_w,
    window6_fin21_facts_certificate_var, window6_fin21_facts_certificate_op,
    window6_first_last_classifier_first, window6_first_last_classifier_last]

end Omega.EA
