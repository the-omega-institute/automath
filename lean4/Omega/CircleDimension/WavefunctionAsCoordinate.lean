import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic

namespace Omega.CircleDimension

universe u v

/-- Concrete data for the basis-dependent coordinate description of a pure state ray. A chosen
representative `rayVector` of the ray and a chosen orthonormal basis are recorded explicitly. -/
structure WavefunctionAsCoordinateData where
  carrier : Type u
  basisIndex : Type v
  [instNormedAddCommGroup : NormedAddCommGroup carrier]
  [instInnerProductSpace : InnerProductSpace ℂ carrier]
  basisVector : basisIndex → carrier
  coordinateMap : basisIndex → carrier → ℂ
  basis_norm : ∀ x, ‖basisVector x‖ = 1
  basis_orthogonal :
    ∀ x y, x ≠ y → coordinateMap x (basisVector y) = 0
  rayVector : carrier
  ray_nonzero : rayVector ≠ 0

attribute [instance] WavefunctionAsCoordinateData.instNormedAddCommGroup
attribute [instance] WavefunctionAsCoordinateData.instInnerProductSpace

namespace WavefunctionAsCoordinateData

/-- The basis-dependent coordinate function of the chosen ray representative. -/
def coordinateFunction (D : WavefunctionAsCoordinateData) (x : D.basisIndex) : ℂ :=
  D.coordinateMap x D.rayVector

/-- The wavefunction attached to the chosen basis is exactly the coordinate function. -/
def wavefunction (D : WavefunctionAsCoordinateData) : D.basisIndex → ℂ :=
  D.coordinateFunction

/-- In the chosen orthonormal basis, the wavefunction is the coordinate function of the selected
ray representative. -/
def wavefunctionIsCoordinate (D : WavefunctionAsCoordinateData) : Prop :=
  ∃ ψ : D.basisIndex → ℂ,
    ψ = D.wavefunction ∧ ∀ x, ψ x = D.coordinateMap x D.rayVector

end WavefunctionAsCoordinateData

open WavefunctionAsCoordinateData

/-- Paper label: `cor:cdim-wavefunction-as-coordinate`. -/
theorem paper_cdim_wavefunction_as_coordinate (D : WavefunctionAsCoordinateData) :
    D.wavefunctionIsCoordinate := by
  refine ⟨D.wavefunction, rfl, ?_⟩
  intro x
  rfl

end Omega.CircleDimension
