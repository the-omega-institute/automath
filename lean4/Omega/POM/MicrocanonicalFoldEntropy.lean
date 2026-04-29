import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.POM.MicrocanonicalFoldClassCount

namespace Omega.POM

open scoped BigOperators

section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The normalized fiber profile `w(x) = d(x) / N`. -/
noncomputable def microcanonicalFoldNormalizedWeight (d : α → ℕ) (x : α) : ℝ :=
  (d x : ℝ) / (microcanonicalTotalMass d : ℝ)

/-- The Shannon entropy of the normalized fiber profile. -/
noncomputable def microcanonicalFoldShannonEntropy (d : α → ℕ) : ℝ :=
  -∑ x : α,
    microcanonicalFoldNormalizedWeight d x * Real.log (microcanonicalFoldNormalizedWeight d x)

/-- The leading entropy term obtained after taking logarithms of the multinomial formula. -/
noncomputable def microcanonicalFoldEntropyMainTerm (d : α → ℕ) : ℝ :=
  -∑ x : α, (d x : ℝ) * Real.log (microcanonicalFoldNormalizedWeight d x)

omit [DecidableEq α] in
private theorem microcanonicalFoldEntropyMainTerm_eq_mul_entropy (d : α → ℕ)
    (hmass : 0 < microcanonicalTotalMass d) :
    microcanonicalFoldEntropyMainTerm d =
      (microcanonicalTotalMass d : ℝ) * microcanonicalFoldShannonEntropy d := by
  have hmass_ne : (microcanonicalTotalMass d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hmass
  have hterm :
      ∀ x : α,
        (microcanonicalTotalMass d : ℝ) *
            (microcanonicalFoldNormalizedWeight d x *
              Real.log (microcanonicalFoldNormalizedWeight d x)) =
          (d x : ℝ) * Real.log (microcanonicalFoldNormalizedWeight d x) := by
    intro x
    dsimp [microcanonicalFoldNormalizedWeight]
    field_simp [hmass_ne]
  symm
  calc
    (microcanonicalTotalMass d : ℝ) * microcanonicalFoldShannonEntropy d
        =
          (microcanonicalTotalMass d : ℝ) *
            (-(∑ x : α,
                microcanonicalFoldNormalizedWeight d x *
                  Real.log (microcanonicalFoldNormalizedWeight d x))) := by
          rfl
    _ =
          -(∑ x : α,
              (microcanonicalTotalMass d : ℝ) *
                (microcanonicalFoldNormalizedWeight d x *
                  Real.log (microcanonicalFoldNormalizedWeight d x))) := by
          rw [mul_neg, Finset.mul_sum]
    _ = -∑ x : α, (d x : ℝ) * Real.log (microcanonicalFoldNormalizedWeight d x) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          exact hterm x
    _ = microcanonicalFoldEntropyMainTerm d := by
          rfl

/-- Paper label: `thm:pom-microcanonical-fold-entropy`. -/
theorem paper_pom_microcanonical_fold_entropy :
    ∀ {α : Type*} [Fintype α] [DecidableEq α] (d : α → ℕ),
      0 < microcanonicalTotalMass d →
        microcanonicalFoldClassCount d =
            Nat.factorial (microcanonicalTotalMass d) /
              ∏ x ∈ (Finset.univ : Finset α), Nat.factorial (d x) ∧
          microcanonicalFoldEntropyMainTerm d =
            (microcanonicalTotalMass d : ℝ) * microcanonicalFoldShannonEntropy d := by
  intro α _ _ d hmass
  refine ⟨(paper_pom_microcanonical_fold_class_count d).2, ?_⟩
  exact microcanonicalFoldEntropyMainTerm_eq_mul_entropy d hmass

end

end Omega.POM
