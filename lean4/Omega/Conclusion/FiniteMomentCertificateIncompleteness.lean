import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-moment incompleteness statement: two distinct positive atomic presentations,
both supported at the visible tail point `1`, produce identical readings for every finite set of
moment exponents. This packages the basic obstruction that finitely many moment queries do not
uniquely determine the underlying atomic presentation. -/
def conclusion_finite_moment_certificate_incompleteness_statement (Q : Finset ℝ) : Prop :=
  ∃ wPlus wMinus : Fin 2 → ℝ,
    wPlus ≠ wMinus ∧
      (∀ i, 0 < wPlus i) ∧
      (∀ i, 0 < wMinus i) ∧
      ∀ q ∈ Q, ∑ i, wPlus i * Real.rpow 1 q = ∑ i, wMinus i * Real.rpow 1 q

/-- Paper label: `thm:conclusion-finite-moment-certificate-incompleteness`. -/
theorem paper_conclusion_finite_moment_certificate_incompleteness (Q : Finset ℝ) :
    conclusion_finite_moment_certificate_incompleteness_statement Q := by
  refine ⟨fun _ => (1 : ℝ), fun i => if i = 0 then (3 / 2 : ℝ) else (1 / 2 : ℝ), ?_, ?_, ?_, ?_⟩
  · intro hEq
    have h0 := congrFun hEq 0
    norm_num at h0
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · intro q hq
    norm_num [Real.one_rpow]

end Omega.Conclusion
