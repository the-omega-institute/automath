import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

universe u v

/-- Concrete data for the multiplicity function on a continuous-spectrum sector and the abstract
Hilbert carrier represented by that sector. The direct-integral model is encoded by the dependent
function space `∀ x, Fin (multiplicity x) → ℂ`. -/
structure CoordinateRepresentationData where
  X : Type u
  sector : Type v
  multiplicity : X → ℕ

namespace CoordinateRepresentationData

/-- The vector-valued direct-integral model attached to the spectral multiplicity function. -/
abbrev DirectIntegralModel (D : CoordinateRepresentationData) :=
  (x : D.X) → Fin (D.multiplicity x) → ℂ

/-- The scalar coordinate model obtained in the multiplicity-one case. -/
abbrev CoordinateModel (D : CoordinateRepresentationData) :=
  D.X → ℂ

/-- The sector admits the continuous-spectrum direct-integral representation. -/
def continuousSpectrumRepresentation (D : CoordinateRepresentationData) : Prop :=
  Nonempty (D.sector ≃ D.DirectIntegralModel)

/-- The multiplicity function degenerates to `1` almost everywhere; in this concrete wrapper, that
means it is identically `1`. -/
def multiplicityOne (D : CoordinateRepresentationData) : Prop :=
  ∀ x, D.multiplicity x = 1

/-- The sector admits the scalar coordinate model `X → ℂ`. -/
def coordinateRepresentation (D : CoordinateRepresentationData) : Prop :=
  Nonempty (D.sector ≃ D.CoordinateModel)

private def uniqueIndex (D : CoordinateRepresentationData) (hOne : D.multiplicityOne)
    (x : D.X) : Fin (D.multiplicity x) :=
  ⟨0, by simp [hOne x]⟩

/-- When every multiplicity space is one-dimensional, the vector-valued direct integral collapses
to the scalar coordinate model. -/
def multiplicityOneDirectIntegralEquiv (D : CoordinateRepresentationData)
    (hOne : D.multiplicityOne) : D.DirectIntegralModel ≃ D.CoordinateModel where
  toFun ψ x := ψ x (uniqueIndex D hOne x)
  invFun f x _ := f x
  left_inv ψ := by
    funext x i
    have hi : (i : ℕ) = 0 := by
      have hi' : (i : ℕ) < 1 := by
        simpa [hOne x] using i.isLt
      omega
    have hEq : i = uniqueIndex D hOne x := by
      apply Fin.ext
      simp [uniqueIndex, hi]
    simp [hEq, uniqueIndex]
  right_inv f := by
    rfl

end CoordinateRepresentationData

open CoordinateRepresentationData

/-- Paper label: `cor:cdim-coordinate-representation`. -/
theorem paper_cdim_coordinate_representation (D : CoordinateRepresentationData) :
    D.continuousSpectrumRepresentation →
      D.multiplicityOne →
        D.coordinateRepresentation := by
  intro hRepresentation hOne
  rcases hRepresentation with ⟨e⟩
  exact ⟨e.trans (multiplicityOneDirectIntegralEquiv D hOne)⟩

end Omega.CircleDimension
