import Mathlib.Tactic
import Omega.Conclusion.Window6VisibleOddCommonQuotient

namespace Omega.Conclusion

noncomputable section

/-- The shell-`2` standard basis vector in the visible odd three-shell space. -/
def conclusion_window6_visible_odd_kernel_basis_e2 :
    conclusion_window6_visible_odd_common_quotient_space :=
  fun i => if i = 0 then 1 else 0

/-- The shell-`3` standard basis vector in the visible odd three-shell space. -/
def conclusion_window6_visible_odd_kernel_basis_e3 :
    conclusion_window6_visible_odd_common_quotient_space :=
  fun i => if i = 1 then 1 else 0

/-- The shell-`4` standard basis vector in the visible odd three-shell space. -/
def conclusion_window6_visible_odd_kernel_basis_e4 :
    conclusion_window6_visible_odd_common_quotient_space :=
  fun i => if i = 2 then 1 else 0

/-- Concrete basis statement for the visible odd common kernel and its visible complement. -/
def conclusion_window6_visible_odd_kernel_basis_statement : Prop :=
  (∀ f : conclusion_window6_visible_odd_common_quotient_space,
    f ∈ conclusion_window6_visible_odd_common_quotient_O1.ker ↔
      ∃ a b : ℂ,
        f = a • conclusion_window6_visible_odd_kernel_basis_e3 +
          b • (conclusion_window6_visible_odd_kernel_basis_e2 +
            conclusion_window6_visible_odd_kernel_basis_e4)) ∧
    conclusion_window6_visible_odd_common_quotient_O1.ker =
      conclusion_window6_visible_odd_common_quotient_O3.ker ∧
    (∀ f : conclusion_window6_visible_odd_common_quotient_space,
      ∃ a b c : ℂ,
        f = a • conclusion_window6_visible_odd_kernel_basis_e3 +
          b • (conclusion_window6_visible_odd_kernel_basis_e2 +
            conclusion_window6_visible_odd_kernel_basis_e4) +
          c • (conclusion_window6_visible_odd_kernel_basis_e4 -
            conclusion_window6_visible_odd_kernel_basis_e2)) ∧
    (∀ a b c : ℂ,
      a • conclusion_window6_visible_odd_kernel_basis_e3 +
          b • (conclusion_window6_visible_odd_kernel_basis_e2 +
            conclusion_window6_visible_odd_kernel_basis_e4) +
          c • (conclusion_window6_visible_odd_kernel_basis_e4 -
            conclusion_window6_visible_odd_kernel_basis_e2) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0)

/-- Paper label: `cor:conclusion-window6-visible-odd-kernel-basis`. -/
theorem paper_conclusion_window6_visible_odd_kernel_basis :
    conclusion_window6_visible_odd_kernel_basis_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f
    constructor
    · intro hf
      have hq : conclusion_window6_visible_odd_common_quotient_q_odd_map f = 0 := by
        simpa [paper_conclusion_window6_visible_odd_common_quotient.1] using hf
      have h20 : f 2 = f 0 := by
        have hz : f 2 - f 0 = 0 := by
          simpa [conclusion_window6_visible_odd_common_quotient_q_odd_map,
            conclusion_window6_visible_odd_common_quotient_q_odd,
            conclusion_window6_visible_odd_common_quotient_shell2,
            conclusion_window6_visible_odd_common_quotient_shell4] using hq
        exact sub_eq_zero.mp hz
      refine ⟨f 1, f 0, ?_⟩
      ext i
      fin_cases i <;>
        simp [conclusion_window6_visible_odd_kernel_basis_e2,
          conclusion_window6_visible_odd_kernel_basis_e3,
          conclusion_window6_visible_odd_kernel_basis_e4, h20]
    · rintro ⟨a, b, rfl⟩
      simp [conclusion_window6_visible_odd_common_quotient_O1,
        conclusion_window6_visible_odd_common_quotient_shell2,
        conclusion_window6_visible_odd_common_quotient_shell4,
        conclusion_window6_visible_odd_kernel_basis_e2,
        conclusion_window6_visible_odd_kernel_basis_e3,
        conclusion_window6_visible_odd_kernel_basis_e4]
  · exact paper_conclusion_window6_visible_odd_common_quotient.2.2.1
  · intro f
    refine ⟨f 1, (f 0 + f 2) / 2, (f 2 - f 0) / 2, ?_⟩
    ext i
    fin_cases i <;>
      simp [conclusion_window6_visible_odd_kernel_basis_e2,
        conclusion_window6_visible_odd_kernel_basis_e3,
        conclusion_window6_visible_odd_kernel_basis_e4] <;>
      ring
  · intro a b c h
    have h0 := congr_fun h 0
    have h1 := congr_fun h 1
    have h2 := congr_fun h 2
    simp [conclusion_window6_visible_odd_kernel_basis_e2,
      conclusion_window6_visible_odd_kernel_basis_e3,
      conclusion_window6_visible_odd_kernel_basis_e4] at h0 h1 h2
    refine ⟨h1, ?_, ?_⟩
    · linear_combination (1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h2
    · linear_combination (-1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h2

end

end Omega.Conclusion
