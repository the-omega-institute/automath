import Omega.SPG.BoundaryGodelDimensionSeparatedUnionMax

namespace Omega.SPG

/-- Paper label: `thm:derived-subfull-boundary-complexity-equals-adhesion`.
This wrapper packages the phase-diagram equality, the bitlength-exponent equality, the
Kolmogorov lower-bound implication, the separated-union max law, and the saturation readout into
one boundary-only complexity statement. -/
theorem paper_derived_subfull_boundary_complexity_equals_adhesion
    (boundaryDimension adhesionDefect bitlengthExponent kolmogorovLower unionBoundaryDimension
      leftAdhesion rightAdhesion ambientDimension : ℝ)
    (hPhase : boundaryDimension = adhesionDefect)
    (hBitlength : bitlengthExponent = adhesionDefect)
    (hKolmogorov : kolmogorovLower ≤ adhesionDefect)
    (hLeft : leftAdhesion ≤ unionBoundaryDimension)
    (hRight : rightAdhesion ≤ unionBoundaryDimension)
    (hUnionUpper : unionBoundaryDimension ≤ max leftAdhesion rightAdhesion)
    (hSaturation : boundaryDimension = ambientDimension) :
    boundaryDimension = adhesionDefect ∧
      bitlengthExponent = adhesionDefect ∧
      kolmogorovLower ≤ adhesionDefect ∧
      unionBoundaryDimension = max leftAdhesion rightAdhesion ∧
      adhesionDefect = ambientDimension := by
  have hUnion :=
    paper_spg_boundary_godel_dimension_separated_union_max
      leftAdhesion rightAdhesion unionBoundaryDimension hLeft hRight hUnionUpper
  refine ⟨hPhase, hBitlength, hKolmogorov, hUnion, ?_⟩
  calc
    adhesionDefect = boundaryDimension := hPhase.symm
    _ = ambientDimension := hSaturation

end Omega.SPG
