import Mathlib.Tactic

namespace Omega.GU

/-- Binary magma terms labelled by variables in `Fin n`. -/
inductive window6_first_last_classifier_term (n : Nat) : Type where
  | window6_first_last_classifier_var : Fin n → window6_first_last_classifier_term n
  | window6_first_last_classifier_mul :
      window6_first_last_classifier_term n →
      window6_first_last_classifier_term n →
      window6_first_last_classifier_term n

/-- The first variable encountered by the left-to-right traversal of a binary term. -/
def window6_first_last_classifier_first {n : Nat} :
    window6_first_last_classifier_term n → Fin n
  | .window6_first_last_classifier_var i => i
  | .window6_first_last_classifier_mul u _ => window6_first_last_classifier_first u

/-- The last variable encountered by the left-to-right traversal of a binary term. -/
def window6_first_last_classifier_last {n : Nat} :
    window6_first_last_classifier_term n → Fin n
  | .window6_first_last_classifier_var i => i
  | .window6_first_last_classifier_mul _ v => window6_first_last_classifier_last v

/-- Evaluation in the CRT rectangular-band model `(a₃, a₇) ⋄ (b₃, b₇) = (a₃, b₇)`. -/
def window6_first_last_classifier_eval {n : Nat} (ρ : Fin n → Fin 3 × Fin 7) :
    window6_first_last_classifier_term n → Fin 3 × Fin 7
  | .window6_first_last_classifier_var i => ρ i
  | .window6_first_last_classifier_mul u v =>
      ((window6_first_last_classifier_eval ρ u).1,
        (window6_first_last_classifier_eval ρ v).2)

/-- In the window-6 rectangular-band model, every term is classified by its first and last
variables: the `Fin 3` coordinate comes from the first variable and the `Fin 7` coordinate from the
last variable.
    lem:window6-first-last-classifier -/
theorem paper_window6_first_last_classifier {n : ℕ}
    (t : window6_first_last_classifier_term n) (ρ : Fin n → Fin 3 × Fin 7) :
    window6_first_last_classifier_eval ρ t =
      ((ρ (window6_first_last_classifier_first t)).1,
        (ρ (window6_first_last_classifier_last t)).2) := by
  induction t with
  | window6_first_last_classifier_var i =>
      rfl
  | window6_first_last_classifier_mul u v hu hv =>
      simp [window6_first_last_classifier_eval, window6_first_last_classifier_first,
        window6_first_last_classifier_last, hu, hv]

end Omega.GU
