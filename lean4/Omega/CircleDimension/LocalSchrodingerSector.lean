import Mathlib
import Omega.CircleDimension.LocalEuclideanSectorPositive
import Omega.CircleDimension.SecondOrderPrincipalSymbol
import Omega.CircleDimension.UnitarySelfAdjointLog
import Omega.CircleDimension.WavefunctionAsCoordinate

namespace Omega.CircleDimension

noncomputable section

/-- Concrete local data for the Euclidean-sector Schrödinger normal form. The Euclidean sector,
principal symbol, local coordinate wavefunction, and a scalar potential term are recorded
explicitly, together with the local coordinate Schrödinger equation. -/
structure LocalSchrodingerSectorData where
  sector : LocalEuclideanSectorData
  symbol : SecondOrderPrincipalSymbolData
  generator : ReadableTimeWordPrincipalPhaseGeneratorData
  wave : WavefunctionAsCoordinateData
  timeDerivative : wave.basisIndex → ℂ
  laplacianTerm : wave.basisIndex → ℂ
  potential : ℂ
  localEquation :
    ∀ x : wave.basisIndex,
      Complex.I * timeDerivative x = laplacianTerm x + potential * wave.wavefunction x

namespace LocalSchrodingerSectorData

/-- The generator has Euclidean normal form when its principal symbol is quadratic and positive,
the local Euclidean sector is positive, and the spectral generator stays in the principal branch. -/
def generatorHasEuclideanNormalForm (D : LocalSchrodingerSectorData) : Prop :=
  D.symbol.HasQuadraticPrincipalSymbol ∧
    (∀ v, v ≠ 0 → 0 < D.sector.quad v) ∧
    D.generator.boundedSelfAdjointGenerator

/-- The local wavefunction is a coordinate wavefunction satisfying the local Schrödinger equation
with Hamiltonian `laplacianTerm + potential * ψ`. -/
def wavefunctionsSatisfyLocalSchrodinger (D : LocalSchrodingerSectorData) : Prop :=
  D.wave.wavefunctionIsCoordinate ∧
    ∀ x : D.wave.basisIndex,
      Complex.I * D.timeDerivative x =
        D.laplacianTerm x + D.potential * D.wave.wavefunction x

end LocalSchrodingerSectorData

open LocalSchrodingerSectorData

/-- Paper label: `thm:cdim-local-schrodinger-sector`. The positive local Euclidean sector and the
quadratic principal-symbol package give the Euclidean normal form, while the coordinate
wavefunction package turns the local evolution identity into the local scalar Schrödinger
equation. -/
theorem paper_cdim_local_schrodinger_sector (D : LocalSchrodingerSectorData) :
    D.generatorHasEuclideanNormalForm ∧ D.wavefunctionsSatisfyLocalSchrodinger := by
  have hSymbol : D.symbol.HasQuadraticPrincipalSymbol :=
    paper_cdim_second_order_principal_symbol D.symbol
  have hSector : ∀ v, v ≠ 0 → 0 < D.sector.quad v :=
    paper_cdim_local_euclidean_sector_positive D.sector
  have hGenerator : D.generator.boundedSelfAdjointGenerator :=
    (paper_cdim_unitary_selfadjoint_log D.generator).1
  have hWave : D.wave.wavefunctionIsCoordinate :=
    paper_cdim_wavefunction_as_coordinate D.wave
  exact ⟨⟨hSymbol, hSector, hGenerator⟩, ⟨hWave, D.localEquation⟩⟩

end

end Omega.CircleDimension
