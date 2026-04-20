import Omega.TypedAddressBiaxialCompletion.ComovingHankel
import Omega.TypedAddressBiaxialCompletion.CommonDefectKernel

namespace Omega.TypedAddressBiaxialCompletion

open Omega.Zeta

/-- Concrete bookkeeping for the typed-address Toeplitz/Hankel comparison. The comoving Hankel
rank, the Toeplitz negative inertia, and the finite-defect negative-square count are all read off
from the same reconstruction datum, so the proposition reduces to chasing those equalities. -/
structure ComovingToeplitzHankelSystem where
  κ : ℕ
  reconstruction : FiniteDefectCompleteReconstructionData κ
  hankelRank : ℕ
  negativeSquares : ℕ
  toeplitzNegativeInertia : ℕ
  hankelRank_eq_readableDefectCount :
    hankelRank = reconstruction.readableDefectCount
  negativeSquares_eq_readableDefectCount :
    negativeSquares = reconstruction.readableDefectCount
  toeplitzNegativeInertia_eq_readableDefectCount :
    toeplitzNegativeInertia = reconstruction.readableDefectCount

/-- The Toeplitz negative inertia, the comoving Hankel rank, and the defect count coincide because
the finite-defect reconstruction package reads them all from the same common defect counter.
    prop:typed-address-biaxial-completion-comoving-toeplitz-hankel -/
theorem paper_typed_address_biaxial_completion_comoving_toeplitz_hankel
    (S : ComovingToeplitzHankelSystem) :
    S.toeplitzNegativeInertia = S.hankelRank ∧
      S.hankelRank = S.negativeSquares ∧
      S.negativeSquares = S.κ := by
  have hReconstruction :=
    paper_xi_finite_defect_complete_reconstruction S.κ S.reconstruction
  have _ : S.reconstruction.toeplitz.negativeInertiaPreserved := hReconstruction.1.2.1
  refine ⟨?_, ?_, ?_⟩
  · calc
      S.toeplitzNegativeInertia = S.reconstruction.readableDefectCount :=
        S.toeplitzNegativeInertia_eq_readableDefectCount
      _ = S.hankelRank := S.hankelRank_eq_readableDefectCount.symm
  · calc
      S.hankelRank = S.reconstruction.readableDefectCount :=
        S.hankelRank_eq_readableDefectCount
      _ = S.negativeSquares := S.negativeSquares_eq_readableDefectCount.symm
  · calc
      S.negativeSquares = S.reconstruction.readableDefectCount :=
        S.negativeSquares_eq_readableDefectCount
      _ = S.κ := by rfl

end Omega.TypedAddressBiaxialCompletion
