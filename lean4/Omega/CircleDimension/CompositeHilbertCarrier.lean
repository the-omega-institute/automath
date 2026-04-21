import Omega.CircleDimension.HilbertCarrier

namespace Omega.CircleDimension

universe u v

/-- Concrete data for the Hilbert carrier of a composite mechanism. The kernel factorization is
recorded on an index product, while `tensorEquiv` identifies the composite quotient carrier with
the product carrier used here as the tensor-product presentation seed. -/
structure CompositeHilbertCarrierData where
  leftIndex : Type u
  rightIndex : Type v
  leftCarrier : ReadableTimeWordHilbertCarrierData
  rightCarrier : ReadableTimeWordHilbertCarrierData
  compositeCarrier : ReadableTimeWordHilbertCarrierData
  leftKernel : leftIndex → leftIndex → ℂ
  rightKernel : rightIndex → rightIndex → ℂ
  compositeKernel : (leftIndex × rightIndex) → (leftIndex × rightIndex) → ℂ
  tensorEquiv :
    compositeCarrier.quotientCarrier ≃
      (leftCarrier.quotientCarrier × rightCarrier.quotientCarrier)

namespace CompositeHilbertCarrierData

/-- The explicit product kernel built from the two component kernels. -/
def tensorProductKernel (D : CompositeHilbertCarrierData) :
    (D.leftIndex × D.rightIndex) → (D.leftIndex × D.rightIndex) → ℂ :=
  fun x y => D.leftKernel x.1 y.1 * D.rightKernel x.2 y.2

/-- Independence means multiplicative kernel factorization on product states. -/
def independentMechanisms (D : CompositeHilbertCarrierData) : Prop :=
  D.compositeKernel = D.tensorProductKernel

/-- The carrier identified with the tensor presentation of the two components. -/
abbrev tensorProductCarrier (D : CompositeHilbertCarrierData) : Type _ :=
  D.leftCarrier.quotientCarrier × D.rightCarrier.quotientCarrier

/-- The composite carrier is presented by the tensor kernel and inherits Hilbert completions from
the component carriers and the composite quotient carrier. -/
def compositeCarrierIsTensorProduct (D : CompositeHilbertCarrierData) : Prop :=
  D.compositeKernel = D.tensorProductKernel ∧
    Nonempty (D.compositeCarrier.quotientCarrier ≃ D.tensorProductCarrier) ∧
    D.leftCarrier.hilbertCompletionExists ∧
    D.rightCarrier.hilbertCompletionExists ∧
    D.compositeCarrier.hilbertCompletionExists

end CompositeHilbertCarrierData

open CompositeHilbertCarrierData

/-- Paper label: `thm:cdim-composite-hilbert-carrier`. -/
theorem paper_cdim_composite_hilbert_carrier (D : CompositeHilbertCarrierData) :
    D.independentMechanisms → D.compositeCarrierIsTensorProduct := by
  intro hIndependent
  rcases paper_cdim_hilbert_carrier D.leftCarrier with ⟨_, hLeftComplete⟩
  rcases paper_cdim_hilbert_carrier D.rightCarrier with ⟨_, hRightComplete⟩
  rcases paper_cdim_hilbert_carrier D.compositeCarrier with ⟨_, hCompositeComplete⟩
  exact ⟨hIndependent, ⟨D.tensorEquiv⟩, hLeftComplete, hRightComplete, hCompositeComplete⟩

end Omega.CircleDimension
