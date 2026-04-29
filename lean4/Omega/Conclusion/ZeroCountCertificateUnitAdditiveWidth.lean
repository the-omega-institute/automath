import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- Concrete asymptotic data for the zero-count certificate interval. -/
structure conclusion_zero_count_certificate_unit_additive_width_data where
  conclusion_zero_count_certificate_unit_additive_width_M : ℕ → ℝ
  conclusion_zero_count_certificate_unit_additive_width_L : ℕ → ℝ
  conclusion_zero_count_certificate_unit_additive_width_U : ℕ → ℝ
  conclusion_zero_count_certificate_unit_additive_width_additiveError : ℕ → ℝ
  conclusion_zero_count_certificate_unit_additive_width_exponentError : ℕ → ℝ
  conclusion_zero_count_certificate_unit_additive_width_additive_identity :
    ∀ m,
      conclusion_zero_count_certificate_unit_additive_width_U m -
          conclusion_zero_count_certificate_unit_additive_width_L m =
        1 - conclusion_zero_count_certificate_unit_additive_width_additiveError m
  conclusion_zero_count_certificate_unit_additive_width_exponent_identity :
    ∀ m,
      Real.log
          (conclusion_zero_count_certificate_unit_additive_width_U m /
            conclusion_zero_count_certificate_unit_additive_width_L m) /
          Real.log (conclusion_zero_count_certificate_unit_additive_width_M m) =
        1 - conclusion_zero_count_certificate_unit_additive_width_exponentError m
  conclusion_zero_count_certificate_unit_additive_width_additive_error_tendsto :
    Tendsto conclusion_zero_count_certificate_unit_additive_width_additiveError atTop (nhds 0)
  conclusion_zero_count_certificate_unit_additive_width_exponent_error_tendsto :
    Tendsto conclusion_zero_count_certificate_unit_additive_width_exponentError atTop (nhds 0)

namespace conclusion_zero_count_certificate_unit_additive_width_data

/-- The additive width and multiplicative logarithmic exponent conclusions. -/
def statement (D : conclusion_zero_count_certificate_unit_additive_width_data) : Prop :=
  Tendsto
      (fun m =>
        D.conclusion_zero_count_certificate_unit_additive_width_U m -
          D.conclusion_zero_count_certificate_unit_additive_width_L m)
      atTop (nhds 1) ∧
    Tendsto
      (fun m =>
        Real.log
            (D.conclusion_zero_count_certificate_unit_additive_width_U m /
              D.conclusion_zero_count_certificate_unit_additive_width_L m) /
            Real.log (D.conclusion_zero_count_certificate_unit_additive_width_M m))
      atTop (nhds 1)

end conclusion_zero_count_certificate_unit_additive_width_data

/-- Paper label: `thm:conclusion-zero-count-certificate-unit-additive-width`. -/
theorem paper_conclusion_zero_count_certificate_unit_additive_width
    (D : conclusion_zero_count_certificate_unit_additive_width_data) : D.statement := by
  constructor
  · have hconst :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have hsub :
        Tendsto
          (fun m : ℕ =>
            1 - D.conclusion_zero_count_certificate_unit_additive_width_additiveError m)
          atTop (nhds (1 - 0)) :=
      hconst.sub D.conclusion_zero_count_certificate_unit_additive_width_additive_error_tendsto
    have hrewrite :
        (fun m : ℕ =>
            D.conclusion_zero_count_certificate_unit_additive_width_U m -
              D.conclusion_zero_count_certificate_unit_additive_width_L m) =
          fun m : ℕ =>
            1 - D.conclusion_zero_count_certificate_unit_additive_width_additiveError m := by
      funext m
      exact D.conclusion_zero_count_certificate_unit_additive_width_additive_identity m
    simpa [conclusion_zero_count_certificate_unit_additive_width_data.statement, hrewrite] using hsub
  · have hconst :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have hsub :
        Tendsto
          (fun m : ℕ =>
            1 - D.conclusion_zero_count_certificate_unit_additive_width_exponentError m)
          atTop (nhds (1 - 0)) :=
      hconst.sub D.conclusion_zero_count_certificate_unit_additive_width_exponent_error_tendsto
    have hrewrite :
        (fun m : ℕ =>
            Real.log
                (D.conclusion_zero_count_certificate_unit_additive_width_U m /
                  D.conclusion_zero_count_certificate_unit_additive_width_L m) /
                Real.log (D.conclusion_zero_count_certificate_unit_additive_width_M m)) =
          fun m : ℕ =>
            1 - D.conclusion_zero_count_certificate_unit_additive_width_exponentError m := by
      funext m
      exact D.conclusion_zero_count_certificate_unit_additive_width_exponent_identity m
    simpa [conclusion_zero_count_certificate_unit_additive_width_data.statement, hrewrite] using hsub

end Omega.Conclusion
