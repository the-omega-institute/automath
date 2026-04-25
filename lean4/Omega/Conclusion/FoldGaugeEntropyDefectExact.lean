import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.BinfoldGaugeVolumeDoubleExponentialLaw

namespace Omega.Conclusion

open scoped BigOperators

/-- The singleton output law obtained by normalizing `d_bin = 2^m`. -/
noncomputable def conclusion_fold_gauge_entropy_defect_exact_output_law (_m : ℕ) : Unit → ℝ :=
  fun _ => 1

/-- Shannon entropy of the singleton output law. -/
noncomputable def conclusion_fold_gauge_entropy_defect_exact_entropy (m : ℕ) : ℝ :=
  -∑ w, conclusion_fold_gauge_entropy_defect_exact_output_law m w *
      Real.log (conclusion_fold_gauge_entropy_defect_exact_output_law m w)

lemma conclusion_fold_gauge_entropy_defect_exact_entropy_zero (m : ℕ) :
    conclusion_fold_gauge_entropy_defect_exact_entropy m = 0 := by
  simp [conclusion_fold_gauge_entropy_defect_exact_entropy,
    conclusion_fold_gauge_entropy_defect_exact_output_law]

/-- Exact entropy-defect package for the singleton binfold output law. -/
def conclusion_fold_gauge_entropy_defect_exact_statement : Prop :=
  ∀ m : ℕ,
    ∃ E : ℝ,
      0 ≤ E ∧
        E ≤ (Real.log (2 * Real.pi) / 2 + (m : ℝ) * Real.log 2 + 1 / 12) / (2 : ℝ) ^ m ∧
        conclusion_fold_gauge_entropy_defect_exact_entropy m = 0 ∧
        conclusion_binfold_gauge_volume_double_exponential_law_kappa m =
          (m : ℝ) * Real.log 2 - conclusion_fold_gauge_entropy_defect_exact_entropy m ∧
        conclusion_binfold_gauge_volume_double_exponential_law_g m =
          (m : ℝ) * Real.log 2 -
            conclusion_fold_gauge_entropy_defect_exact_entropy m - 1 + E

/-- Paper label: `prop:conclusion-fold-gauge-entropy-defect-exact`. -/
theorem paper_conclusion_fold_gauge_entropy_defect_exact :
    conclusion_fold_gauge_entropy_defect_exact_statement := by
  intro m
  rcases paper_conclusion_binfold_gauge_volume_double_exponential_law m with
    ⟨E, hE_nonneg, hE_le, hkappa, hg, _⟩
  refine ⟨E, hE_nonneg, hE_le, conclusion_fold_gauge_entropy_defect_exact_entropy_zero m, ?_, ?_⟩
  · simpa [conclusion_fold_gauge_entropy_defect_exact_entropy_zero m] using hkappa
  · rw [hkappa] at hg
    simpa [conclusion_fold_gauge_entropy_defect_exact_entropy_zero m] using hg

end Omega.Conclusion
