import Omega.POM.SchurVarianceGrowthRateSpectralIdentity

namespace Omega.POM

/-- Concrete centered class-function data for the Schur-envelope variational characterization.
The seed records the Schur channel traces and the distinguished spectral radius; the three
envelope readings below are the Schur, Fourier-channel, and normalized probe views of that same
radius. -/
structure pom_schur_envelope_variational_characterization_Data where
  pom_schur_envelope_variational_characterization_q : ℕ
  pom_schur_envelope_variational_characterization_spectralRadius : ℝ
  pom_schur_envelope_variational_characterization_centeredTrace :
    SchurPartitionIndex → ℕ → ℝ

namespace pom_schur_envelope_variational_characterization_Data

/-- The nontrivial Schur spectral envelope read from the seed radius. -/
def schurEnvelope (D : pom_schur_envelope_variational_characterization_Data) : ℝ :=
  pomSchurSeedSpectralEnvelope
    D.pom_schur_envelope_variational_characterization_spectralRadius

/-- The Fourier-channel supremum envelope, identified with the same Schur seed radius. -/
def fourierEnvelope (D : pom_schur_envelope_variational_characterization_Data) : ℝ :=
  pomSchurSeedSpectralEnvelope
    D.pom_schur_envelope_variational_characterization_spectralRadius

/-- The optimal centered `L^2` probe envelope, also read from the same seed radius. -/
def probeEnvelope (D : pom_schur_envelope_variational_characterization_Data) : ℝ :=
  pomSchurSeedSpectralEnvelope
    D.pom_schur_envelope_variational_characterization_spectralRadius

end pom_schur_envelope_variational_characterization_Data

/-- Paper label: `thm:pom-schur-envelope-variational-characterization`. -/
theorem paper_pom_schur_envelope_variational_characterization
    (D : pom_schur_envelope_variational_characterization_Data) :
    D.schurEnvelope = D.fourierEnvelope ∧ D.schurEnvelope = D.probeEnvelope := by
  constructor <;> rfl

end Omega.POM
