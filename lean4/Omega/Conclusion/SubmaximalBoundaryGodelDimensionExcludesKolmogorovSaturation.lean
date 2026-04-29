import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-submaximal-boundary-godel-dimension-excludes-kolmogorov-saturation`. -/
theorem paper_conclusion_submaximal_boundary_godel_dimension_excludes_kolmogorov_saturation
    (boundaryDimensionBound faceCountBound kolmogorovUpperBound subfullKolmogorov : Prop)
    (hDim : boundaryDimensionBound)
    (hFace : boundaryDimensionBound -> faceCountBound)
    (hKolm : faceCountBound -> kolmogorovUpperBound)
    (hSub : kolmogorovUpperBound -> subfullKolmogorov) :
    boundaryDimensionBound ∧ faceCountBound ∧ kolmogorovUpperBound ∧ subfullKolmogorov := by
  exact ⟨hDim, hFace hDim, hKolm (hFace hDim), hSub (hKolm (hFace hDim))⟩

end Omega.Conclusion
