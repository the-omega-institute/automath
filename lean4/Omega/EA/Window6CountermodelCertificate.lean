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

end Omega.EA
