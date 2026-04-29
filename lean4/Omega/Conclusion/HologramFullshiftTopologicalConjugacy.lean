import Mathlib.Tactic
import Omega.Conclusion.CanonicalFixedpointFullshiftConjugacy

namespace Omega.Conclusion

noncomputable section

/-- The hologram image `𝓧` is represented by the coded fixed-point model. -/
abbrev conclusion_hologram_fullshift_topological_conjugacy_image (D : CanonicalSliceData) :=
  CanonicalFixedpointCode D

/-- The hologram coordinate map from digit streams into `𝓧`. -/
def conclusion_hologram_fullshift_topological_conjugacy_map (D : CanonicalSliceData) :
    CanonicalDigitStream D → conclusion_hologram_fullshift_topological_conjugacy_image D :=
  canonicalDigitEncoder D

/-- The transported shift on the hologram image. -/
def conclusion_hologram_fullshift_topological_conjugacy_shift (D : CanonicalSliceData) :
    conclusion_hologram_fullshift_topological_conjugacy_image D →
      conclusion_hologram_fullshift_topological_conjugacy_image D :=
  canonicalCodeShift D

/-- Fixed-point counts for the transported hologram dynamics. -/
def conclusion_hologram_fullshift_topological_conjugacy_fixed_point_count
    (D : CanonicalSliceData) (n : ℕ) : ℕ :=
  Fintype.card (D.fixedPointsAtLayer n)

/-- Topological entropy of the transported full shift. -/
def conclusion_hologram_fullshift_topological_conjugacy_entropy
    (D : CanonicalSliceData) : ℝ :=
  Real.log (D.M + 1)

/-- Artin--Mazur zeta function of the transported full shift. -/
def conclusion_hologram_fullshift_topological_conjugacy_artin_mazur_zeta
    (D : CanonicalSliceData) (z : ℚ) : ℚ :=
  1 / (1 - (D.M + 1 : ℚ) * z)

/-- Paper label: `thm:conclusion-hologram-fullshift-topological-conjugacy`. The previously
formalized canonical affine conjugacy transports the one-sided full shift to the hologram image;
the conjugacy package then gives the standard fixed-point counts, entropy, and Artin--Mazur zeta
formula for the transported system. -/
theorem paper_conclusion_hologram_fullshift_topological_conjugacy :
    ∀ D : CanonicalSliceData,
      CanonicalFixedpointFullshiftConjugacyStatement D ∧
        Function.Bijective (conclusion_hologram_fullshift_topological_conjugacy_map D) ∧
        (∀ n : ℕ,
          conclusion_hologram_fullshift_topological_conjugacy_fixed_point_count D (n + 1) =
            (D.M + 1) ^ (n + 1)) ∧
        conclusion_hologram_fullshift_topological_conjugacy_entropy D = Real.log (D.M + 1) ∧
        (∀ z : ℚ,
          conclusion_hologram_fullshift_topological_conjugacy_artin_mazur_zeta D z =
            1 / (1 - (D.M + 1 : ℚ) * z)) := by
  intro D
  refine ⟨paper_conclusion_canonical_fixedpoint_fullshift_conjugacy D,
    ⟨(canonicalDigitEquiv D).bijective, ⟨?_, ⟨rfl, ?_⟩⟩⟩⟩
  · intro n
    simpa [conclusion_hologram_fullshift_topological_conjugacy_fixed_point_count] using
      (paper_conclusion_canonical_slice_exact_fixedpoint_count D (n + 1)).2
  · intro z
    rfl

end

end Omega.Conclusion
