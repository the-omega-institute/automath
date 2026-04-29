import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Count of a fixed escort symbol in a finite sample. -/
def conclusion_fixed_sample_escort_count_shell_sufficiency_count
    {n Q : Nat} (x : Fin n → Fin Q) (a : Fin Q) : Nat :=
  (Finset.univ.filter fun i => x i = a).card

/-- Count shell equivalence for fixed-sample escort observations. -/
def conclusion_fixed_sample_escort_count_shell_sufficiency_sameShell
    {n Q : Nat} (x y : Fin n → Fin Q) : Prop :=
  ∀ a : Fin Q,
    conclusion_fixed_sample_escort_count_shell_sufficiency_count x a =
      conclusion_fixed_sample_escort_count_shell_sufficiency_count y a

/-- A decision risk that factors through the fixed-sample escort count shell. -/
def conclusion_fixed_sample_escort_count_shell_sufficiency_risk
    {n Q : Nat} (loss : (Fin Q → Nat) → ℝ) (x : Fin n → Fin Q) : ℝ :=
  loss fun a => conclusion_fixed_sample_escort_count_shell_sufficiency_count x a

/-- Paper-facing fixed-sample escort count-shell sufficiency statement. -/
def conclusion_fixed_sample_escort_count_shell_sufficiency_statement
    (n Q : Nat) : Prop :=
  ∀ (loss : (Fin Q → Nat) → ℝ) (x y : Fin n → Fin Q),
    conclusion_fixed_sample_escort_count_shell_sufficiency_sameShell x y →
      conclusion_fixed_sample_escort_count_shell_sufficiency_risk loss x =
        conclusion_fixed_sample_escort_count_shell_sufficiency_risk loss y

/-- Paper label: `thm:conclusion-fixed-sample-escort-count-shell-sufficiency`. -/
theorem paper_conclusion_fixed_sample_escort_count_shell_sufficiency (n Q : Nat) :
    conclusion_fixed_sample_escort_count_shell_sufficiency_statement n Q := by
  intro loss x y hxy
  unfold conclusion_fixed_sample_escort_count_shell_sufficiency_risk
  exact congrArg loss (funext hxy)

end Omega.Conclusion
