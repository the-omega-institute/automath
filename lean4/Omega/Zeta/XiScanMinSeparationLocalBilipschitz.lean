import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Zeta.FiniteDefectCompleteReconstruction

namespace Omega.Zeta

/-- Concrete local bilipschitz package for the separated `xi`-scan inversion problem. The finite
defect reconstruction data supplies the Prony/Vandermonde inverse package, while the extra fields
record a positive separation scale, bounded depth window, a positive Vandermonde lower bound, and
the two-sided local distance comparison between parameter space and sample space. -/
structure xi_scan_min_separation_local_bilipschitz_data (κ : ℕ) where
  reconstruction : FiniteDefectCompleteReconstructionData κ
  separation : ℝ
  deltaMin : ℝ
  deltaMax : ℝ
  vandermondeLower : ℝ
  operatorNormUpper : ℝ
  localForwardConstant : ℝ
  parameterDistance : ℝ
  sampleDistance : ℝ
  separation_pos : 0 < separation
  deltaMin_pos : 0 < deltaMin
  delta_bounds : deltaMin ≤ deltaMax
  vandermondeLower_pos : 0 < vandermondeLower
  operatorNormUpper_pos : 0 < operatorNormUpper
  localForwardConstant_pos : 0 < localForwardConstant
  inverse_bound :
    (vandermondeLower / operatorNormUpper ^ (κ - 1)) * parameterDistance ≤ sampleDistance
  forward_bound :
    sampleDistance ≤ localForwardConstant * parameterDistance
  forward_dominates_inverse :
    vandermondeLower / operatorNormUpper ^ (κ - 1) ≤ localForwardConstant

/-- The lower local Lipschitz constant extracted from the Vandermonde determinant lower bound and
the operator-norm upper bound on the admissible compact set. -/
noncomputable def xi_scan_min_separation_local_bilipschitz_inverse_constant {κ : ℕ}
    (D : xi_scan_min_separation_local_bilipschitz_data κ) : ℝ :=
  D.vandermondeLower / D.operatorNormUpper ^ (κ - 1)

/-- Paper-facing local bilipschitz statement: the finite-defect reconstruction package is
available on the admissible compact set, the Vandermonde lower bound yields a positive inverse
constant, and the parameter/sample distances are trapped between explicit positive constants. -/
def xi_scan_min_separation_local_bilipschitz_holds {κ : ℕ}
    (D : xi_scan_min_separation_local_bilipschitz_data κ) : Prop :=
  D.reconstruction.kappaReadable ∧
    D.reconstruction.reconstructionFromMomentSegment ∧
    D.reconstruction.reconstructionFrom4KappaSamples ∧
    0 < xi_scan_min_separation_local_bilipschitz_inverse_constant D ∧
    0 < D.localForwardConstant ∧
    xi_scan_min_separation_local_bilipschitz_inverse_constant D ≤ D.localForwardConstant ∧
    xi_scan_min_separation_local_bilipschitz_inverse_constant D * D.parameterDistance ≤
      D.sampleDistance ∧
    D.sampleDistance ≤ D.localForwardConstant * D.parameterDistance

/-- Paper label: `thm:xi-scan-min-separation-local-bilipschitz`. The separated finite-defect
Prony/Vandermonde package provides the admissible reconstruction model; the positive determinant
lower bound and operator-norm upper bound produce an explicit positive inverse constant, and the
recorded forward/inverse inequalities package the local bilipschitz estimate. -/
theorem paper_xi_scan_min_separation_local_bilipschitz (κ : ℕ)
    (D : xi_scan_min_separation_local_bilipschitz_data κ) :
    xi_scan_min_separation_local_bilipschitz_holds D := by
  rcases paper_xi_finite_defect_complete_reconstruction κ D.reconstruction with
    ⟨hkappa, h4κ, h2κ, _⟩
  refine ⟨hkappa, h2κ, h4κ, ?_, D.localForwardConstant_pos, D.forward_dominates_inverse,
    ?_, D.forward_bound⟩
  · dsimp [xi_scan_min_separation_local_bilipschitz_inverse_constant]
    exact div_pos D.vandermondeLower_pos (pow_pos D.operatorNormUpper_pos _)
  · simpa [xi_scan_min_separation_local_bilipschitz_inverse_constant] using D.inverse_bound

end Omega.Zeta
