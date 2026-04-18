import Mathlib.Tactic

namespace Omega.Conclusion

/-- Scalar model of the Green-side matrix entry `A = D⁻¹ (L + d dᵀ / Vol)`. -/
noncomputable def kirchhoffGreenUpdatedEntry (D L dOne vol : ℝ) : ℝ :=
  D⁻¹ * (L + dOne ^ 2 / vol)

/-- Clearing the `D⁻¹` and `Vol⁻¹` denominators leaves the adjugate-style numerator. -/
noncomputable def kirchhoffGreenClearedDeterminant (D L dOne vol : ℝ) : ℝ :=
  D * vol * kirchhoffGreenUpdatedEntry D L dOne vol

/-- The matrix-tree contribution after clearing denominators. -/
noncomputable def kirchhoffTreeTerm (L vol : ℝ) : ℝ :=
  vol * L

/-- The rank-one determinant-lemma contribution after clearing denominators. -/
noncomputable def kirchhoffRankOneTerm (dOne : ℝ) : ℝ :=
  dOne ^ 2

/-- After using `dᵀ 1 = Vol(G)`, the determinant identity collapses to a single scalar formula. -/
noncomputable def kirchhoffGreenDeterminantNormalForm (L vol : ℝ) : ℝ :=
  vol * (L + vol)

/-- Writing `A = D⁻¹ (L + d dᵀ / Vol)`, clearing denominators, and substituting `dᵀ1 = Vol(G)`
gives the determinant identity: the numerator splits into the Kirchhoff cofactor term and the
rank-one update, hence equals `Vol(G) * (L + Vol(G))`.
    thm:conclusion-kirchhoff-green-determinant-identity -/
theorem paper_conclusion_kirchhoff_green_determinant_identity
    (D L dOne vol : ℝ) (hD : D ≠ 0) (hvol : vol ≠ 0) (hdOne : dOne = vol) :
    kirchhoffGreenClearedDeterminant D L dOne vol =
        kirchhoffTreeTerm L vol + kirchhoffRankOneTerm dOne ∧
      kirchhoffGreenClearedDeterminant D L dOne vol =
        kirchhoffGreenDeterminantNormalForm L vol := by
  refine ⟨?_, ?_⟩
  · unfold kirchhoffGreenClearedDeterminant kirchhoffGreenUpdatedEntry
    unfold kirchhoffTreeTerm kirchhoffRankOneTerm
    field_simp [hD, hvol]
  · rw [hdOne]
    unfold kirchhoffGreenClearedDeterminant kirchhoffGreenUpdatedEntry
    unfold kirchhoffGreenDeterminantNormalForm
    field_simp [hD, hvol]

end Omega.Conclusion
