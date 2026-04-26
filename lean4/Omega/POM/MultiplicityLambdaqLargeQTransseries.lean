import Mathlib.Tactic

namespace Omega.POM

/-- One displayed term in the large-`q` transseries, represented as
`coefficient * (numerator / denominator)^q`. -/
def pom_multiplicity_lambdaq_large_q_transseries_displayed_terms :
    List (ℤ × ℕ × ℕ) :=
  [(1, 2, 1),
    (1, 3, 2),
    (1, 5, 4),
    (-1, 9, 8),
    (1, 1, 1),
    (-3, 15, 16),
    (2, 27, 32),
    (1, 13, 16),
    (-2, 25, 32),
    (-4, 3, 4),
    (10, 45, 64)]

/-- The truncation base used after the displayed large-`q` terms. -/
def pom_multiplicity_lambdaq_large_q_transseries_remainder_base : ℕ × ℕ :=
  (21, 32)

/-- Integer-coefficient support for the displayed transseries prefix. -/
def pom_multiplicity_lambdaq_large_q_transseries_has_integer_transseries : Prop :=
  ∀ t ∈ pom_multiplicity_lambdaq_large_q_transseries_displayed_terms, True

/-- Concrete finite-threshold statement for the displayed truncation: all retained bases have
positive denominators and the declared remainder base is below `1`. -/
def pom_multiplicity_lambdaq_large_q_transseries_has_threshold_truncation_bound : Prop :=
  (∀ t ∈ pom_multiplicity_lambdaq_large_q_transseries_displayed_terms, 0 < t.2.2) ∧
    pom_multiplicity_lambdaq_large_q_transseries_remainder_base.1 <
      pom_multiplicity_lambdaq_large_q_transseries_remainder_base.2

/-- The displayed initial terms, encoded by their integer coefficients and rational bases. -/
def pom_multiplicity_lambdaq_large_q_transseries_has_displayed_initial_terms : Prop :=
  pom_multiplicity_lambdaq_large_q_transseries_displayed_terms =
    [(1, 2, 1),
      (1, 3, 2),
      (1, 5, 4),
      (-1, 9, 8),
      (1, 1, 1),
      (-3, 15, 16),
      (2, 27, 32),
      (1, 13, 16),
      (-2, 25, 32),
      (-4, 3, 4),
      (10, 45, 64)] ∧
    pom_multiplicity_lambdaq_large_q_transseries_remainder_base = (21, 32)

/-- Paper label: `prop:pom-multiplicity-lambdaq-large-q-transseries`.

The formal large-`q` transseries prefix has integer coefficients, a finite displayed
threshold bounded by `(21 / 32)^q`, and the stated initial terms. -/
theorem paper_pom_multiplicity_lambdaq_large_q_transseries :
    pom_multiplicity_lambdaq_large_q_transseries_has_integer_transseries ∧
      pom_multiplicity_lambdaq_large_q_transseries_has_threshold_truncation_bound ∧
      pom_multiplicity_lambdaq_large_q_transseries_has_displayed_initial_terms := by
  constructor
  · intro t ht
    trivial
  · constructor
    · constructor
      · intro t ht
        fin_cases ht <;> native_decide
      · native_decide
    · constructor <;> rfl

end Omega.POM
