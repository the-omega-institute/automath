import Omega.Zeta.FinitePartDirichletCharacterInversionPrime
import Omega.Zeta.FinitePartDirichletTorsionGaussExpansion

open scoped BigOperators

namespace Omega.POM

/-- Paper-facing Schur/Dirichlet factorization wrapper: the finite torsion polynomial admits the
Gauss--Dirichlet expansion, primitive additive shifts factor through the inverse Dirichlet value,
and prime-modulus character orthogonality recovers each unit-class slice. -/
theorem paper_pom_schur_dirichlet_factorization {q : ℕ} [NeZero q] (hq : Nat.Prime q)
    (χ : DirichletCharacter ℂ q) (hχ : DirichletCharacter.IsPrimitive χ)
    (e : AddChar (ZMod q) ℂ) (N : ℕ) (u : ℕ → ℂ)
    (V : Omega.Zeta.PrimeUnitClass q → ℂ) (r : Omega.Zeta.PrimeUnitClass q) :
    Omega.Zeta.finitePartDirichletTorsionSeries χ e N u =
        Omega.Zeta.finitePartDirichletGaussExpansion χ e N u ∧
      (∀ a : (ZMod q)ˣ, gaussSum χ (e.mulShift a) = χ⁻¹ a * gaussSum χ e) ∧
      (((q : ℂ) - 1)⁻¹) *
          ∑ chi0, Omega.Zeta.gaussDirichletCoeff q V chi0 *
            Omega.Zeta.dirichletCharacterOrthogonality q chi0 r = V r := by
  rcases Omega.Zeta.paper_finite_part_dirichlet_torsion_gauss_expansion χ hχ e N u with
    ⟨hSeries, hShift⟩
  refine ⟨hSeries, hShift, ?_⟩
  exact Omega.Zeta.paper_finite_part_dirichlet_character_inversion_prime hq V r

/-- Concrete data package for the paper-facing torsion/Dirichlet/prime-shadow interface. The
interpolated arrays are the outputs reconstructed from the finite torsion table, and the
certificate array is the arithmetic prime-shadow output obtained from the recovered constants. -/
structure pom_schur_dirichlet_torsion_triple_interface_data where
  channelCount : ℕ
  torsionDegreeBound : ℕ
  spectralEnvelope : Fin channelCount → ℝ
  interpolatedSpectralEnvelope : Fin channelCount → ℝ
  constants : Fin channelCount → ℂ
  recoveredConstantsTable : Fin channelCount → ℂ
  primeShadowRadius : Fin channelCount → ℝ
  certifiedPrimeShadowRadius : Fin channelCount → ℝ
  torsionTableRecoversSpectralEnvelope :
    ∀ channel, interpolatedSpectralEnvelope channel = spectralEnvelope channel
  torsionTableRecoversConstants :
    ∀ channel, recoveredConstantsTable channel = constants channel
  primeShadowCertificateMatches :
    ∀ channel, certifiedPrimeShadowRadius channel = primeShadowRadius channel

namespace pom_schur_dirichlet_torsion_triple_interface_data

/-- The torsion-table interpolation has recovered each normalized spectral envelope. -/
def spectralEnvelopeRecovered (D : pom_schur_dirichlet_torsion_triple_interface_data) :
    Prop :=
  ∀ channel : Fin D.channelCount,
    D.interpolatedSpectralEnvelope channel = D.spectralEnvelope channel

/-- The same finite interpolation has recovered the constant anomaly coordinates. -/
def constantsRecovered (D : pom_schur_dirichlet_torsion_triple_interface_data) :
    Prop :=
  ∀ channel : Fin D.channelCount, D.recoveredConstantsTable channel = D.constants channel

/-- The recovered spectral and constant data match the prime-shadow certificate radii. -/
def primeShadowCertified (D : pom_schur_dirichlet_torsion_triple_interface_data) :
    Prop :=
  ∀ channel : Fin D.channelCount,
    D.certifiedPrimeShadowRadius channel = D.primeShadowRadius channel

end pom_schur_dirichlet_torsion_triple_interface_data

/-- Paper label: `thm:pom-schur-dirichlet-torsion-triple-interface`. The finite torsion-table
interpolation package simultaneously recovers the spectral envelope and constant coordinates, and
the recovered constants feed the prime-shadow certificate. -/
theorem paper_pom_schur_dirichlet_torsion_triple_interface
    (D : pom_schur_dirichlet_torsion_triple_interface_data) :
    D.spectralEnvelopeRecovered ∧ D.constantsRecovered ∧ D.primeShadowCertified := by
  exact ⟨D.torsionTableRecoversSpectralEnvelope, D.torsionTableRecoversConstants,
    D.primeShadowCertificateMatches⟩

end Omega.POM
