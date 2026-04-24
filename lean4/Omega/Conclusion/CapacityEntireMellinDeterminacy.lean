import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic
import Omega.Folding.FiberTruncatedMomentCompleteInversion
import Omega.Folding.FoldNegativeMomentsCapacityMellin

namespace Omega.Conclusion

open Omega.Folding

noncomputable section

/-- The entire Mellin generating function attached to the audited `{2,3,4}` fiber histogram. -/
def conclusion_capacity_entire_mellin_determinacy_entire_mellin (m : ℕ) (s : ℂ) : ℂ :=
  (foldTruncatedHistogram2 m : ℂ) * ((2 : ℂ) ^ s) +
    (foldTruncatedHistogram3 m : ℂ) * ((3 : ℂ) ^ s) +
    (foldTruncatedHistogram4 m : ℂ) * ((4 : ℂ) ^ s)

/-- The concrete continuous-capacity curve used by the audited `{2,3,4}` model. -/
def conclusion_capacity_entire_mellin_determinacy_capacity_curve (m : ℕ) (T : ℝ) : ℝ :=
  foldNegativeMomentCapacityCurve m T

private theorem conclusion_capacity_entire_mellin_determinacy_entire_mellin_zero (m : ℕ) :
    conclusion_capacity_entire_mellin_determinacy_entire_mellin m 0 = (3 * m + 3 : ℂ) := by
  simp [conclusion_capacity_entire_mellin_determinacy_entire_mellin, foldTruncatedHistogram2,
    foldTruncatedHistogram3, foldTruncatedHistogram4]
  ring

private theorem conclusion_capacity_entire_mellin_determinacy_capacity_curve_one (m : ℕ) :
    conclusion_capacity_entire_mellin_determinacy_capacity_curve m 1 = (3 * m + 3 : ℝ) := by
  simpa [conclusion_capacity_entire_mellin_determinacy_capacity_curve] using
    (paper_fold_negative_moments_capacity_mellin m (p := 1) (by norm_num)).2.1

private theorem conclusion_capacity_entire_mellin_determinacy_capacity_curve_two (m : ℕ) :
    conclusion_capacity_entire_mellin_determinacy_capacity_curve m 2 = (6 * m + 6 : ℝ) := by
  simpa [conclusion_capacity_entire_mellin_determinacy_capacity_curve] using
    (paper_fold_negative_moments_capacity_mellin m (p := 1) (by norm_num)).2.2.1

private theorem conclusion_capacity_entire_mellin_determinacy_capacity_curve_four (m : ℕ) :
    conclusion_capacity_entire_mellin_determinacy_capacity_curve m 4 = (9 * m + 7 : ℝ) := by
  simpa [conclusion_capacity_entire_mellin_determinacy_capacity_curve] using
    (paper_fold_negative_moments_capacity_mellin m (p := 1) (by norm_num)).2.2.2.1

/-- Paper label: `thm:conclusion-capacity-entire-mellin-determinacy`. In the audited
`{2,3,4}`-support model, the continuous capacity curve and the entire Mellin generating function
carry exactly the same parameter `m`, so each one uniquely determines the other. -/
theorem paper_conclusion_capacity_entire_mellin_determinacy (m : ℕ) :
    (∀ m' : ℕ,
      (∀ T : ℝ,
        conclusion_capacity_entire_mellin_determinacy_capacity_curve m T =
          conclusion_capacity_entire_mellin_determinacy_capacity_curve m' T) →
      conclusion_capacity_entire_mellin_determinacy_entire_mellin m =
        conclusion_capacity_entire_mellin_determinacy_entire_mellin m') ∧
      (∀ m' : ℕ,
        conclusion_capacity_entire_mellin_determinacy_entire_mellin m =
          conclusion_capacity_entire_mellin_determinacy_entire_mellin m' →
        ∀ T : ℝ,
          conclusion_capacity_entire_mellin_determinacy_capacity_curve m T =
            conclusion_capacity_entire_mellin_determinacy_capacity_curve m' T) := by
  refine ⟨?_, ?_⟩
  · intro m' hcurve
    have h1 : conclusion_capacity_entire_mellin_determinacy_capacity_curve m 1 =
        conclusion_capacity_entire_mellin_determinacy_capacity_curve m' 1 := hcurve 1
    rw [conclusion_capacity_entire_mellin_determinacy_capacity_curve_one,
      conclusion_capacity_entire_mellin_determinacy_capacity_curve_one] at h1
    have hm_real : (m : ℝ) = m' := by
      nlinarith
    have hm : m = m' := by
      exact_mod_cast hm_real
    subst hm
    rfl
  · intro m' hentire T
    have h0 :
        conclusion_capacity_entire_mellin_determinacy_entire_mellin m 0 =
          conclusion_capacity_entire_mellin_determinacy_entire_mellin m' 0 := by
      simpa using congrFun hentire 0
    rw [conclusion_capacity_entire_mellin_determinacy_entire_mellin_zero,
      conclusion_capacity_entire_mellin_determinacy_entire_mellin_zero] at h0
    have hm_nat : 3 * m + 3 = 3 * m' + 3 := by
      exact_mod_cast h0
    have hm : m = m' := by
      omega
    subst hm
    rfl

end

end Omega.Conclusion
