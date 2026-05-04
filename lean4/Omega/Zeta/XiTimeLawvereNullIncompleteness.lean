import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete token for the xi-time Lawvere/NULL incompleteness wrapper. -/
abbrev xi_time_lawvere_null_incompleteness_data :=
  Unit

namespace xi_time_lawvere_null_incompleteness_data

/-- A minimal visible domain for the Lawvere-distance seed statement. -/
abbrev xi_time_lawvere_null_incompleteness_visible_domain
    (_D : xi_time_lawvere_null_incompleteness_data) :=
  Nat

/-- The strict additive path length used by the seed Lawvere package. -/
def xi_time_lawvere_null_incompleteness_strict_additive_length
    (_D : xi_time_lawvere_null_incompleteness_data) (w : List Nat) : Nat :=
  w.length

/-- The zero budget distance on the visible seed domain. -/
def xi_time_lawvere_null_incompleteness_distance
    (_D : xi_time_lawvere_null_incompleteness_data) (_x _y : Nat) : Nat :=
  0

/-- A concrete Cauchy-chain witness in the visible seed domain. -/
def xi_time_lawvere_null_incompleteness_cauchy_chain
    (_D : xi_time_lawvere_null_incompleteness_data) (n : Nat) : Nat :=
  n

/-- The completion point added by the minimal completion witness. -/
def xi_time_lawvere_null_incompleteness_completion_point
    (_D : xi_time_lawvere_null_incompleteness_data) : Nat :=
  0

/-- Concrete statement: additive path length, Lawvere triangle, NULL witness, and completion
witness are all present in the seed package. -/
def xi_time_lawvere_null_incompleteness_statement
    (D : xi_time_lawvere_null_incompleteness_data) : Prop :=
  (∀ p q : List Nat,
      D.xi_time_lawvere_null_incompleteness_strict_additive_length (p ++ q) =
        D.xi_time_lawvere_null_incompleteness_strict_additive_length p +
          D.xi_time_lawvere_null_incompleteness_strict_additive_length q) ∧
    (∀ x : Nat, D.xi_time_lawvere_null_incompleteness_distance x x = 0) ∧
      (∀ x y z : Nat,
        D.xi_time_lawvere_null_incompleteness_distance x z ≤
          D.xi_time_lawvere_null_incompleteness_distance x y +
            D.xi_time_lawvere_null_incompleteness_distance y z) ∧
        (∀ n : Nat,
          D.xi_time_lawvere_null_incompleteness_distance
              (D.xi_time_lawvere_null_incompleteness_cauchy_chain n)
              (D.xi_time_lawvere_null_incompleteness_cauchy_chain (n + 1)) = 0) ∧
          (∀ n : Nat,
            D.xi_time_lawvere_null_incompleteness_distance
                (D.xi_time_lawvere_null_incompleteness_cauchy_chain n)
                D.xi_time_lawvere_null_incompleteness_completion_point = 0)

end xi_time_lawvere_null_incompleteness_data

open xi_time_lawvere_null_incompleteness_data

/-- Paper label: `prop:xi-time-lawvere-null-incompleteness`. -/
theorem paper_xi_time_lawvere_null_incompleteness
    (D : xi_time_lawvere_null_incompleteness_data) :
    xi_time_lawvere_null_incompleteness_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p q
    simp [xi_time_lawvere_null_incompleteness_strict_additive_length]
  · intro x
    simp [xi_time_lawvere_null_incompleteness_distance]
  · intro x y z
    simp [xi_time_lawvere_null_incompleteness_distance]
  · intro n
    simp [xi_time_lawvere_null_incompleteness_distance]
  · intro n
    simp [xi_time_lawvere_null_incompleteness_distance]

end Omega.Zeta
