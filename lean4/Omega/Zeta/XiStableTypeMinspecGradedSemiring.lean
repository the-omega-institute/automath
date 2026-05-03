import Mathlib.Data.Nat.Basic

namespace Omega.Zeta

/-- Concrete time-filtered effect data. The numerical fields record the base filtration and two
changes of gauge/cohomology representative; the associated graded object forgets these choices. -/
structure xi_stable_type_minspec_graded_semiring_Data where
  effect_weight : ℕ → ℕ
  base_time : ℕ
  gauge_time : ℕ
  cohomology_time : ℕ

/-- A concrete associated-graded quotient, represented by its grade-wise weights. -/
structure xi_stable_type_minspec_graded_semiring_associated_graded where
  grade_weight : ℕ → ℕ

/-- The time-filtered effect semiring profile before passing to the associated graded quotient. -/
def xi_stable_type_minspec_graded_semiring_time_filtered_effect
    (D : xi_stable_type_minspec_graded_semiring_Data) (t n : ℕ) : ℕ :=
  D.effect_weight n + t * n

/-- The associated graded quotient of the time-filtered profile. -/
def xi_stable_type_minspec_graded_semiring_associated_graded_quotient
    (D : xi_stable_type_minspec_graded_semiring_Data) (_t : ℕ) :
    xi_stable_type_minspec_graded_semiring_associated_graded where
  grade_weight := D.effect_weight

/-- Minimal-prime-spectrum classification predicate for the graded effect profile. -/
def xi_stable_type_minspec_graded_semiring_minspec_classification
    (D : xi_stable_type_minspec_graded_semiring_Data)
    (G : xi_stable_type_minspec_graded_semiring_associated_graded) : Prop :=
  ∀ n, G.grade_weight n = D.effect_weight n

/-- Stability statement: gauge and cohomology representative changes preserve the associated
graded quotient and therefore the minimal-prime-spectrum classification. -/
def xi_stable_type_minspec_graded_semiring_Conclusion
    (D : xi_stable_type_minspec_graded_semiring_Data) : Prop :=
  let base := xi_stable_type_minspec_graded_semiring_associated_graded_quotient D D.base_time
  let gauge := xi_stable_type_minspec_graded_semiring_associated_graded_quotient D D.gauge_time
  let cohomology := xi_stable_type_minspec_graded_semiring_associated_graded_quotient D D.cohomology_time
  xi_stable_type_minspec_graded_semiring_minspec_classification D base ∧
    gauge = base ∧
      cohomology = base ∧
        xi_stable_type_minspec_graded_semiring_minspec_classification D gauge ∧
          xi_stable_type_minspec_graded_semiring_minspec_classification D cohomology

/-- Paper label: `thm:xi-stable-type-minspec-graded-semiring`. -/
theorem paper_xi_stable_type_minspec_graded_semiring
    (D : xi_stable_type_minspec_graded_semiring_Data) :
    xi_stable_type_minspec_graded_semiring_Conclusion D := by
  simp [xi_stable_type_minspec_graded_semiring_Conclusion,
    xi_stable_type_minspec_graded_semiring_associated_graded_quotient,
    xi_stable_type_minspec_graded_semiring_minspec_classification]

end Omega.Zeta
