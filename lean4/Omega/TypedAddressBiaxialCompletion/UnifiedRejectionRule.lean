import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.BoundaryEndpointOrthogonal
import Omega.TypedAddressBiaxialCompletion.BoundaryJointSufficiency
import Omega.TypedAddressBiaxialCompletion.CertificateLoop
import Omega.TypedAddressBiaxialCompletion.CompiledDefectCertificate
import Omega.TypedAddressBiaxialCompletion.ReadUsTypedPrecision

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete input for the unified rejection-rule package. It records the address-side readout,
the compiled defect certificate, and the Toeplitz/endpoint witnesses used by the offline verifier.
-/
structure UnifiedRejectionWitness where
  address : AddrUS
  verifier : TypedCertificate → Bool
  certificate? : Option TypedCertificate
  defectCertificate : CompiledDefectCertificateData
  offlineVerified : defectCertificate.offlineVerified
  boundaryVerifier : BoundaryJointVerifierData
  endpointHeat : BoundaryEndpointHeatData
  toeplitzCertificate : CompiledToeplitzPsdCertificate
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  radius_lt_one : radius < 1

namespace UnifiedRejectionWitness

/-- Address consistency is the front-interface/`Read_US` package specialized to the concrete
typed-address witness stored in the unified verifier. -/
def addressConsistency (U : UnifiedRejectionWitness) : Prop :=
  (∃ comp : AddrUS → AddrUS,
      ∃ phase : AddrUS → AddrUS,
        ∃ addr : AddrUS → AddrUS,
          ∃ read : AddrUS → ReadUSOutput,
            ∃ audit : ReadUSOutput → ReadUSOutput,
              ∃ spec : ReadUSOutput → ReadUSOutput,
                comp = (readUsFrontInterface U.verifier
                  (fun x => if x = U.address then U.certificate? else none)).comp ∧
                  phase = (readUsFrontInterface U.verifier
                    (fun x => if x = U.address then U.certificate? else none)).phase ∧
                    addr = (readUsFrontInterface U.verifier
                      (fun x => if x = U.address then U.certificate? else none)).addr ∧
                      read = (readUsFrontInterface U.verifier
                        (fun x => if x = U.address then U.certificate? else none)).Read_US ∧
                        audit = (readUsFrontInterface U.verifier
                          (fun x => if x = U.address then U.certificate? else none)).audit ∧
                          spec = (readUsFrontInterface U.verifier
                            (fun x => if x = U.address then U.certificate? else none)).spec) ∧
    (Read_US U.address U.verifier U.certificate? = ReadUSOutput.NonZero ∨
      Read_US U.address U.verifier U.certificate? = ReadUSOutput.RootInterval ∨
      Read_US U.address U.verifier U.certificate? = ReadUSOutput.NULL) ∧
    (Read_US U.address U.verifier U.certificate? = ReadUSOutput.NULL ↔
      U.certificate? = none ∨
        ∃ cert, U.certificate? = some cert ∧
          (precisionCompatible U.address cert = false ∨ U.verifier cert = false))

/-- Defect compilation is the concrete zero-free subdisk output plus the implication from certified
radius convergence to the RH-style sufficiency statement. -/
def defectCompilation (U : UnifiedRejectionWitness) : Prop :=
  U.defectCertificate.zeroFreeSubdisk ∧
    (U.defectCertificate.certifiedRadiusTendsToOne → U.defectCertificate.rhSufficient)

/-- The linear-algebra branch combines the compiled Toeplitz--PSD witness with the endpoint-heat
package and the endpoint non-substitutability clause from the joint verifier. -/
def toeplitzPsdEndpointBranch (U : UnifiedRejectionWitness) : Prop :=
  compiledToeplitzTrueBlockPsd U.toeplitzCertificate ∧
    0 ≤ compiledToeplitzCaratheodoryLowerBound U.toeplitzCertificate U.radius ∧
    0 < compiledToeplitzSchurDelta U.toeplitzCertificate U.radius ∧
    compiledToeplitzSchurBound U.toeplitzCertificate U.radius < 1 ∧
    ((U.boundaryVerifier.axes.radiusBlindspotClosed ∧
        U.boundaryVerifier.axes.addressCollisionClosed ∧
        U.boundaryVerifier.axes.endpointHeatClosed ∧
        U.boundaryVerifier.toeplitzPsdPassed) →
      U.boundaryVerifier.verifierResult = .certificate) ∧
    (U.endpointHeat.monotoneToEndpointAtom ∧
      U.endpointHeat.exponentialErrorBound ∧
      U.endpointHeat.minDepthFormula) ∧
    ((U.boundaryVerifier.axes.radiusBlindspotClosed ∧
        U.boundaryVerifier.axes.addressCollisionClosed ∧
        ¬ U.boundaryVerifier.axes.endpointHeatClosed) →
      U.boundaryVerifier.verifierResult ≠ .certificate)

end UnifiedRejectionWitness

open UnifiedRejectionWitness

/-- Paper label: `prop:typed-address-biaxial-completion-unified-rejection-rule`. -/
theorem paper_typed_address_biaxial_completion_unified_rejection_rule
    (U : UnifiedRejectionWitness) :
    U.addressConsistency ∧ U.defectCompilation ∧ U.toeplitzPsdEndpointBranch := by
  have hAddr :=
    paper_typed_address_biaxial_completion_read_us_typed_precision
      U.address U.verifier U.certificate?
  have hDefect :=
    paper_typed_address_biaxial_completion_compiled_defect_certificate
      U.defectCertificate U.offlineVerified
  have hPsd :=
    paper_typed_address_biaxial_completion_compiled_psd_certificate
      U.toeplitzCertificate U.radius_nonneg U.radius_lt_one
  have hJoint :=
    paper_typed_address_biaxial_completion_boundary_joint_sufficiency
      U.boundaryVerifier
  have hEndpoint :=
    paper_typed_address_biaxial_completion_boundary_endpoint_orthogonal
      U.boundaryVerifier U.endpointHeat
  refine ⟨hAddr, hDefect, ?_⟩
  exact ⟨hPsd.1, hPsd.2.1, hPsd.2.2.1, hPsd.2.2.2, hJoint.1, hEndpoint.1, hEndpoint.2⟩

end Omega.TypedAddressBiaxialCompletion
