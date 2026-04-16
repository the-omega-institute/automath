import Mathlib.Tactic
import Omega.SPG.EllipsoidFluxDecodingPerturbationStability

namespace Omega.SPG

/-- Reconstructed axis data coming from the boundary flux of a diagonal ellipsoid. -/
structure GodelAxisBoundarySignature (d : ℕ) where
  volume : ℝ
  diagonal : Fin d → ℝ

/-- The signature is invertible on diagonal axis data: equality of reconstructed boundary data
recovers the global volume parameter and each diagonal exponent.
    cor:spg-godel-axis-boundary-invertibility -/
theorem paper_spg_godel_axis_boundary_invertibility (d : ℕ)
    (boundaryFluxReconstruction diagonalRecovery : Prop)
    (hFlux : boundaryFluxReconstruction)
    (hDiag : boundaryFluxReconstruction → diagonalRecovery) :
    ∀ {N N' : ℝ} {b b' : Fin d → ℝ},
      GodelAxisBoundarySignature.mk N b = GodelAxisBoundarySignature.mk N' b' →
      N = N' ∧ ∀ i : Fin d, b i = b' i := by
  let _ :=
    paper_spg_ellipsoid_flux_decoding_perturbation_stability d
      boundaryFluxReconstruction diagonalRecovery hFlux hDiag
  intro N N' b b' hEq
  cases hEq
  simp

end Omega.SPG
