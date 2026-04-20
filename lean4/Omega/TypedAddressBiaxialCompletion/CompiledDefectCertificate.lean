import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.CertificateLoop
import Omega.TypedAddressBiaxialCompletion.HorizonPurityRepulsion

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete compiled Jensen-defect certificate data. The record keeps the compiled loop witness,
the radius/defect sequences used by the offline verifier, and the transport from the sequential
radius certificate into the chapter's repulsion-radius node of the certificate loop. -/
structure CompiledDefectCertificateData where
  certificateLoop : TypedAddressCertificateLoopData
  defect : ℕ → ℝ
  rho : ℕ → ℝ
  rho_pos : ∀ n : ℕ, 0 < rho n
  rho_le_one : ∀ n : ℕ, rho n ≤ 1
  repulsion_eq : ∀ n : ℕ, repulsionRadius (rho n) (defect n) = rho n
  tendsto_implies_loopRepulsion :
    radiiTendToOne rho → certificateLoop.repulsionRadiusTendsToOne

namespace CompiledDefectCertificateData

/-- The offline verifier has checked the nonnegativity side condition for every compiled layer. -/
def offlineVerified (C : CompiledDefectCertificateData) : Prop :=
  ∀ n : ℕ, 0 ≤ C.defect n

/-- Every compiled layer exports the zero-free subdisk certificate recorded by the repulsion bound. -/
def zeroFreeSubdisk (C : CompiledDefectCertificateData) : Prop :=
  ∀ n : ℕ, repulsionRadiusZeroFreeCertificate (C.rho n) (C.defect n)

/-- The certified repulsion radii converge to the boundary point `1`. -/
def certifiedRadiusTendsToOne (C : CompiledDefectCertificateData) : Prop :=
  radiiTendToOne C.rho

/-- The compiled certificate is sufficient both in the chapter-local certificate loop and in the
concrete horizon-purity formulation. -/
def rhSufficient (C : CompiledDefectCertificateData) : Prop :=
  C.certificateLoop.rh ∧ rhHorizonPurity C.defect

end CompiledDefectCertificateData

/-- Paper-facing compiled defect certificate wrapper: an offline-verified compiled Jensen-defect
certificate gives the pointwise zero-free subdisk witness, and any certified convergence of the
repulsion radii to `1` is sufficient for both the certificate-loop RH clause and the concrete
horizon-purity statement.
    prop:typed-address-biaxial-completion-compiled-defect-certificate -/
theorem paper_typed_address_biaxial_completion_compiled_defect_certificate
    (C : CompiledDefectCertificateData) :
    C.offlineVerified → C.zeroFreeSubdisk ∧ (C.certifiedRadiusTendsToOne → C.rhSufficient) := by
  intro hOffline
  have hLoop := paper_typed_address_biaxial_completion_certificate_loop C.certificateLoop
  refine ⟨?_, ?_⟩
  · intro n
    exact repulsion_radius_zero_free_certificate (C.rho_pos n) (C.rho_le_one n) (hOffline n)
  · intro hTend
    have hLoopRep : C.certificateLoop.repulsionRadiusTendsToOne :=
      C.tendsto_implies_loopRepulsion hTend
    have hLoopJensen : C.certificateLoop.jensenDefectZeroLimit := (hLoop.2.1).mpr hLoopRep
    have hLoopRh : C.certificateLoop.rh := (hLoop.1).mpr hLoopJensen
    have hPurity : rhHorizonPurity C.defect :=
      repulsion_radius_tends_to_one_implies_rh C.defect C.rho hTend C.rho_pos C.repulsion_eq
    exact ⟨hLoopRh, hPurity⟩

end Omega.TypedAddressBiaxialCompletion
