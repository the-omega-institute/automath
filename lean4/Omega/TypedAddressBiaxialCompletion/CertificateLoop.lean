import Mathlib.Tactic
import Omega.CircleDimension.UnitarySliceDecidable
import Omega.TypedAddressBiaxialCompletion.JensenDefectFiniteization
import Omega.TypedAddressBiaxialCompletion.ThreeEndBudget

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local package for the paper-facing certificate-loop theorem. The fields encode the
unitary-slice lock, the Jensen-defect/repulsion equivalence chain, and the Toeplitz--PSD
cofinality reduction needed for the offline verifier. -/
structure TypedAddressCertificateLoopData where
  unitarySliceLocked : Prop
  rh : Prop
  jensenDefectZeroLimit : Prop
  repulsionRadiusTendsToOne : Prop
  toeplitzPsdAll : Prop
  toeplitzPsdCofinal : Prop
  unitarySliceLocked_h : unitarySliceLocked
  deriveRhIffJensenDefectZeroLimit :
    unitarySliceLocked → (rh ↔ jensenDefectZeroLimit)
  deriveJensenDefectZeroLimitIffRepulsionRadiusTendsToOne :
    unitarySliceLocked → (jensenDefectZeroLimit ↔ repulsionRadiusTendsToOne)
  deriveRepulsionRadiusTendsToOneIffToeplitzPsdAll :
    unitarySliceLocked → (repulsionRadiusTendsToOne ↔ toeplitzPsdAll)
  deriveToeplitzPsdAllIffToeplitzPsdCofinal :
    toeplitzPsdAll ↔ toeplitzPsdCofinal

/-- Paper-facing wrapper theorem for the biaxial completion certificate loop: on the unitary
slice, the RH certificate, the vanishing Jensen-defect limit, the repulsion-radius condition,
full Toeplitz positivity, and its cofinal restriction are the same offline certificate viewed in
different coordinate systems.
    thm:typed-address-biaxial-completion-certificate-loop -/
theorem paper_typed_address_biaxial_completion_certificate_loop
    (D : TypedAddressCertificateLoopData) :
    (D.rh ↔ D.jensenDefectZeroLimit) ∧
      (D.jensenDefectZeroLimit ↔ D.repulsionRadiusTendsToOne) ∧
      (D.repulsionRadiusTendsToOne ↔ D.toeplitzPsdAll) ∧
      (D.toeplitzPsdAll ↔ D.toeplitzPsdCofinal) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact D.deriveRhIffJensenDefectZeroLimit D.unitarySliceLocked_h
  · exact D.deriveJensenDefectZeroLimitIffRepulsionRadiusTendsToOne D.unitarySliceLocked_h
  · exact D.deriveRepulsionRadiusTendsToOneIffToeplitzPsdAll D.unitarySliceLocked_h
  · exact D.deriveToeplitzPsdAllIffToeplitzPsdCofinal

end Omega.TypedAddressBiaxialCompletion
