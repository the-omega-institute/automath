import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.GU

/-- Concrete basis data for the golden quadratic field tensored with the coarse cubic spectrum
field. The product-basis equivalences encode the coprime-degree compositum and the induced audit
algebra basis. -/
structure Window6GoldenCubicAuditFieldData where
  CompositumBasis : Type*
  AuditBasis : Type*
  instFintypeCompositumBasis : Fintype CompositumBasis
  instFintypeAuditBasis : Fintype AuditBasis
  compositumBasisEquiv : CompositumBasis ≃ Fin 2 × Fin 3
  auditBasisEquiv : AuditBasis ≃ Fin 2 × Fin 3

attribute [instance] Window6GoldenCubicAuditFieldData.instFintypeCompositumBasis
attribute [instance] Window6GoldenCubicAuditFieldData.instFintypeAuditBasis

/-- The compositum degree read off from the explicit `2 × 3` product basis. -/
def Window6GoldenCubicAuditFieldData.compositumDegree
    (D : Window6GoldenCubicAuditFieldData) : ℕ :=
  Fintype.card D.CompositumBasis

/-- The audit algebra dimension read off from the same six-element product basis. -/
def Window6GoldenCubicAuditFieldData.auditAlgebraDimension
    (D : Window6GoldenCubicAuditFieldData) : ℕ :=
  Fintype.card D.AuditBasis

/-- Paper label: `cor:window6-golden-cubic-audit-field-degree6`.
The quadratic golden basis and cubic coarse-spectrum basis combine into a six-element product
basis for both the compositum field and its audit algebra. -/
theorem paper_window6_golden_cubic_audit_field_degree6
    (D : Window6GoldenCubicAuditFieldData) :
    D.compositumDegree = 6 ∧ D.auditAlgebraDimension = 6 := by
  refine ⟨?_, ?_⟩
  · simpa [Window6GoldenCubicAuditFieldData.compositumDegree] using
      Fintype.card_congr D.compositumBasisEquiv
  · simpa [Window6GoldenCubicAuditFieldData.auditAlgebraDimension] using
      Fintype.card_congr D.auditBasisEquiv

end Omega.GU
