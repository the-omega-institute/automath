import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.POM.ProjectivePathAtomicPronyRank

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The multiplicity carried by the atoms that attain the chosen maximal slope. -/
def derived_projective_path_maxplus_intercept_leading_intercept
    (D : ProjectivePathAtomicPronyData) (a : Fin D.atomCount) : ℤ :=
  Finset.sum (Finset.univ.filter (fun b : Fin D.atomCount => D.theta b = D.theta a)) fun b =>
    (D.multiplicity b : ℤ)

/-- The residual multiplicity carried by the strictly smaller slopes. -/
def derived_projective_path_maxplus_intercept_tail
    (D : ProjectivePathAtomicPronyData) (a : Fin D.atomCount) : ℤ :=
  Finset.sum (Finset.univ.filter (fun b : Fin D.atomCount => D.theta b ≠ D.theta a)) fun b =>
    (D.multiplicity b : ℤ)

/-- Concrete max-plus intercept package for the fixed-length projective-path Prony model. Any
chosen maximal atom supplies the leading intercept, the `q = 0` moment splits into leading and tail
parts, and every tail slope is strictly smaller than the leading slope. -/
def derived_projective_path_maxplus_intercept_statement (D : ProjectivePathAtomicPronyData) :
    Prop :=
  (∀ a : Fin D.atomCount,
      (∀ b : Fin D.atomCount, D.theta b ≤ D.theta a) →
        projectivePathMoment D 0 =
            derived_projective_path_maxplus_intercept_leading_intercept D a +
              derived_projective_path_maxplus_intercept_tail D a ∧
          ∀ b : Fin D.atomCount, D.theta b ≠ D.theta a → D.theta b < D.theta a) ∧
    (D.atomCount = 0 → projectivePathMoment D 0 = 0)

/-- Paper label: `thm:derived-projective-path-maxplus-intercept`. -/
theorem paper_derived_projective_path_maxplus_intercept (D : ProjectivePathAtomicPronyData) :
    derived_projective_path_maxplus_intercept_statement D := by
  refine ⟨?_, ?_⟩
  · intro a hmax
    refine ⟨?_, ?_⟩
    · calc
        projectivePathMoment D 0
            = ∑ b : Fin D.atomCount, (D.multiplicity b : ℤ) := by
                simp [projectivePathMoment]
        _ =
            derived_projective_path_maxplus_intercept_leading_intercept D a +
              derived_projective_path_maxplus_intercept_tail D a := by
                rw [← Finset.sum_filter_add_sum_filter_not
                  (s := (Finset.univ : Finset (Fin D.atomCount)))
                  (p := fun b : Fin D.atomCount => D.theta b = D.theta a)
                  (f := fun b : Fin D.atomCount => (D.multiplicity b : ℤ))]
                simp [derived_projective_path_maxplus_intercept_leading_intercept,
                  derived_projective_path_maxplus_intercept_tail]
    · intro b hb
      exact lt_of_le_of_ne (hmax b) hb
  · intro hzero
    cases D
    cases hzero
    simp [projectivePathMoment]

end

end Omega.POM
