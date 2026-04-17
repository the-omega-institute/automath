import Omega.Zeta.FiniteDefectCompleteReconstruction

namespace Omega.TypedAddressBiaxialCompletion

open Omega.Zeta

/-- Concrete data for the common defect kernel statement.  The readable defect count coming from
finite reconstruction is identified with both the negative-square count and the Toeplitz negative
inertia count. -/
structure TypedAddressCommonDefectKernelData where
  kappa : ℕ
  negativeSquares : ℕ
  toeplitzNegativeInertia : ℕ
  reconstruction : FiniteDefectCompleteReconstructionData kappa
  negativeSquares_eq_readableDefectCount :
    negativeSquares = reconstruction.readableDefectCount
  toeplitzNegativeInertia_eq_readableDefectCount :
    toeplitzNegativeInertia = reconstruction.readableDefectCount

/-- The negative-square count and the Toeplitz negative inertia are both read off from the same
finite-defect reconstruction datum, so they agree with the common defect count `κ`.
    prop:typed-address-biaxial-completion-common-defect-kernel -/
theorem paper_typed_address_biaxial_completion_common_defect_kernel
    (D : TypedAddressCommonDefectKernelData) :
    D.kappa = D.negativeSquares ∧ D.kappa = D.toeplitzNegativeInertia := by
  have hReconstruction :=
    paper_xi_finite_defect_complete_reconstruction D.kappa D.reconstruction
  have _ : D.reconstruction.toeplitz.negativeInertiaPreserved := hReconstruction.1.2.1
  refine ⟨?_, ?_⟩
  · calc
      D.kappa = D.reconstruction.readableDefectCount := by rfl
      _ = D.negativeSquares := D.negativeSquares_eq_readableDefectCount.symm
  · calc
      D.kappa = D.reconstruction.readableDefectCount := by rfl
      _ = D.toeplitzNegativeInertia := D.toeplitzNegativeInertia_eq_readableDefectCount.symm

end Omega.TypedAddressBiaxialCompletion
