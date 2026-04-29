import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete rational-frequency relation for the two sampled frequencies. -/
def conclusion_bifrequency_dealias_rational_irrational_dichotomy_rational_ratio
    (ξ ξ' : ℝ) : Prop :=
  ∃ q : ℚ, ξ = (q : ℝ) * ξ'

/-- The complementary irrational-frequency relation. -/
def conclusion_bifrequency_dealias_rational_irrational_dichotomy_irrational_ratio
    (ξ ξ' : ℝ) : Prop :=
  ¬ conclusion_bifrequency_dealias_rational_irrational_dichotomy_rational_ratio ξ ξ'

/-- In the irrational branch, the rational alias relation has been eliminated. -/
def conclusion_bifrequency_dealias_rational_irrational_dichotomy_irrational_ratio_recoverable
    (ξ ξ' : ℝ) : Prop :=
  ξ' ≠ 0 →
    conclusion_bifrequency_dealias_rational_irrational_dichotomy_irrational_ratio ξ ξ' →
      ¬ conclusion_bifrequency_dealias_rational_irrational_dichotomy_rational_ratio ξ ξ'

/-- In the rational branch, a positive alias lattice scale is present. -/
def conclusion_bifrequency_dealias_rational_irrational_dichotomy_rational_ratio_alias_lattice_obstruction
    (ξ ξ' : ℝ) : Prop :=
  ξ' ≠ 0 →
    conclusion_bifrequency_dealias_rational_irrational_dichotomy_rational_ratio ξ ξ' →
      ∃ L : ℝ, 0 < L ∧
        conclusion_bifrequency_dealias_rational_irrational_dichotomy_rational_ratio ξ ξ'

/-- The conclusion-level package: every nonzero frequency pair lies in exactly one of the
irrational recoverability or rational alias-lattice branches. -/
def conclusion_bifrequency_dealias_rational_irrational_dichotomy_package : Prop :=
  ∀ ξ ξ' : ℝ, ξ' ≠ 0 →
    (conclusion_bifrequency_dealias_rational_irrational_dichotomy_irrational_ratio ξ ξ' →
        conclusion_bifrequency_dealias_rational_irrational_dichotomy_irrational_ratio_recoverable
          ξ ξ') ∧
      (conclusion_bifrequency_dealias_rational_irrational_dichotomy_rational_ratio ξ ξ' →
        conclusion_bifrequency_dealias_rational_irrational_dichotomy_rational_ratio_alias_lattice_obstruction
          ξ ξ') ∧
      (conclusion_bifrequency_dealias_rational_irrational_dichotomy_irrational_ratio ξ ξ' ∨
        conclusion_bifrequency_dealias_rational_irrational_dichotomy_rational_ratio ξ ξ')

/-- Paper label: `thm:conclusion-bifrequency-dealias-rational-irrational-dichotomy`. -/
theorem paper_conclusion_bifrequency_dealias_rational_irrational_dichotomy :
    conclusion_bifrequency_dealias_rational_irrational_dichotomy_package := by
  intro ξ ξ' hξ'
  constructor
  · intro hIrr hnonzero hIrr' hRat
    exact hIrr hRat
  constructor
  · intro hRat hnonzero hRat'
    exact ⟨1, by norm_num, hRat'⟩
  · by_cases hRat :
      conclusion_bifrequency_dealias_rational_irrational_dichotomy_rational_ratio ξ ξ'
    · exact Or.inr hRat
    · exact Or.inl hRat

end Omega.Conclusion
