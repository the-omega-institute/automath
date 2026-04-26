import Mathlib.Tactic
import Omega.Conclusion.ArithmeticDoubleTransversalTerminalNormalForm
import Omega.POM.ProjectionBudget

namespace Omega.Conclusion

open Omega.POM.DoubleTransversalNormalForm

/-- The terminal two-axis readout keeps only the value fiber and the symmetric remainder. -/
noncomputable def conclusion_arithmetic_terminal_two_axis_completeness_terminal_readout
    (a : Omega.POM.DoubleTransversalNormalForm.Config) (b : ℕ) : ℤ × ℤ :=
  (Val a, Pi_b (Val a) b)

/-- The terminal readout is complete if it is uniquely determined by the value and remainder axes,
and the quotient is recoverable from those two coordinates alone. -/
def conclusion_arithmetic_terminal_two_axis_completeness_two_axis_readout
    (a : Omega.POM.DoubleTransversalNormalForm.Config) (b : ℕ) : Prop :=
  ∃! axes : ℤ × ℤ,
    axes = conclusion_arithmetic_terminal_two_axis_completeness_terminal_readout a b ∧
      InFiber_b b axes.2 ∧
      ((Val a - axes.2) / (b : ℤ)) * (b : ℤ) + axes.2 = Val a

/-- Paper label: `cor:conclusion-arithmetic-terminal-two-axis-completeness`. The projection-budget
corollary lets both terminal projections be deferred to the end, the double-transversal normal
form provides the exact decomposition `Val(x) = qb + r`, and therefore the quotient is recovered
from `(Val(x), r)` as `q = (Val(x) - r) / b`. -/
theorem paper_conclusion_arithmetic_terminal_two_axis_completeness
    (D : Omega.POM.ExtendedPrimitiveData) (a : Omega.POM.DoubleTransversalNormalForm.Config)
    (b : ℕ) (hb : 0 < b) :
    Omega.POM.PomProjectionBudget D ∧
      conclusion_arithmetic_terminal_two_axis_completeness_two_axis_readout a b ∧
      ∀ q r : ℤ, Val a = q * (b : ℤ) + r →
        r = Pi_b (Val a) b →
        q = (Val a - r) / (b : ℤ) := by
  have hbudget : Omega.POM.PomProjectionBudget D := Omega.POM.paper_pom_projection_budget D
  have hnormal : existsUniqueNormalForm a b :=
    paper_conclusion_arithmetic_double_transversal_terminal_normal_form a b hb
  rcases hnormal with ⟨triple, htriple, _huniq⟩
  rcases htriple with ⟨_hfold, hr, hq, hfiber, _hvalfold, hdecomp⟩
  have hformula :
      ((Val a - Pi_b (Val a) b) / (b : ℤ)) * (b : ℤ) + Pi_b (Val a) b = Val a := by
    calc
      ((Val a - Pi_b (Val a) b) / (b : ℤ)) * (b : ℤ) + Pi_b (Val a) b
          = triple.2.1 * (b : ℤ) + triple.2.2 := by simp [hr, hq]
      _ = Val a := by simpa using hdecomp.symm
  refine ⟨hbudget, ?_, ?_⟩
  · refine ⟨conclusion_arithmetic_terminal_two_axis_completeness_terminal_readout a b, ?_, ?_⟩
    · refine ⟨rfl, ?_, hformula⟩
      simpa [conclusion_arithmetic_terminal_two_axis_completeness_terminal_readout, hr] using hfiber
    · intro axes haxes
      rcases haxes with ⟨hreadout, _hinFiber, _hformula'⟩
      simp [hreadout]
  · intro q r hval hr'
    subst hr'
    have hbz : (b : ℤ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hb
    have hsub : Val a - Pi_b (Val a) b = q * (b : ℤ) := by
      linarith
    calc
      q = (q * (b : ℤ)) / (b : ℤ) := by
            symm
            simpa [mul_comm] using Int.mul_ediv_cancel_left q hbz
      _ = (Val a - Pi_b (Val a) b) / (b : ℤ) := by rw [← hsub]

end Omega.Conclusion
