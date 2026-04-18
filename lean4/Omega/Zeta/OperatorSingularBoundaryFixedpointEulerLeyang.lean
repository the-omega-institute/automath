import Omega.SyncKernelWeighted.IharaWittPrimitiveSpectrum

namespace Omega.Zeta

open Omega.SyncKernelWeighted

/-- The fixed-point and Euler-product presentations of the chapter-local weighted zeta package
agree because both specialize to the same Witt-coordinate family. -/
abbrev singularBoundaryFixedpointZeta (K : WeightedHashimotoTraceData) :=
  weightedHashimotoWittExponential K

/-- Euler-product presentation of the same chapter-local weighted zeta package. -/
abbrev singularBoundaryEulerProduct (K : WeightedHashimotoTraceData) :=
  weightedHashimotoWittEulerProduct K

/-- Coefficient readout used for the fixed-point/Euler comparison. -/
abbrev singularBoundaryPrimitiveCoefficient (K : WeightedHashimotoTraceData) (n k : ℕ) :=
  weightedHashimotoEnergyCoefficient K n k

/-- Paper-facing fixed-point/Euler package: the chapter-local fixed-point zeta presentation agrees
with the Euler-product presentation, and the coefficient readout may be taken from either side. -/
theorem paper_operator_singular_boundary_fixedpoint_zeta_euler
    (K : WeightedHashimotoTraceData) :
    singularBoundaryFixedpointZeta K = singularBoundaryEulerProduct K ∧
      ∀ n k,
        singularBoundaryPrimitiveCoefficient K n k =
          (singularBoundaryEulerProduct K n).coeff k := by
  rcases paper_ihara_witt_primitive_spectrum K with ⟨hExp, hEuler, hCoeff⟩
  refine ⟨hExp.trans hEuler.symm, ?_⟩
  intro n k
  simpa [singularBoundaryPrimitiveCoefficient, singularBoundaryEulerProduct, hEuler] using hCoeff n k

end Omega.Zeta
