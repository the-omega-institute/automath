import Mathlib.Data.Complex.Basic
import Omega.Conclusion.PrimitiveMinimalCarrierQuotient

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete determinant-channel data for the minimal visible quotient statement. The determinant
profile is expanded on a finite family of active channels, and the coefficient-detection witness is
the existing hypothesis used by the primitive minimal-carrier theorem. -/
structure conclusion_artin_determinant_minimal_visible_quotient_data where
  G : Type*
  X : Type*
  instFintypeG : Fintype G
  instCommGroupG : CommGroup G
  active : Finset X
  channel : X → G → Complex
  coeff : X → Complex
  determinantProfile : G → Complex
  channel_one : ∀ x, channel x 1 = 1
  channel_mul : ∀ x g h, channel x (g * h) = channel x g * channel x h
  determinant_expansion :
    ∀ g, determinantProfile g = Finset.sum active (fun x => channel x g * coeff x)
  coeff_detects_kernel :
    ∀ k,
      (∀ c,
          Finset.sum active (fun x => channel x c * ((channel x k - 1) * coeff x)) = 0) →
        k ∈ @primitiveMinimalCarrierKernel G X instCommGroupG active channel channel_one channel_mul

attribute [instance]
  conclusion_artin_determinant_minimal_visible_quotient_data.instFintypeG
attribute [instance]
  conclusion_artin_determinant_minimal_visible_quotient_data.instCommGroupG

namespace conclusion_artin_determinant_minimal_visible_quotient_data

/-- The determinant-active channel intersection `N_det`. -/
def N_det (D : conclusion_artin_determinant_minimal_visible_quotient_data) : Subgroup D.G := by
  letI := D.instCommGroupG
  exact primitiveMinimalCarrierKernel D.active D.channel D.channel_one D.channel_mul

/-- Quotienting by `N_det` preserves exactly the active determinant factors. -/
def minimal_quotient_preserves_determinant
    (D : conclusion_artin_determinant_minimal_visible_quotient_data) : Prop :=
  by
    letI := D.instCommGroupG
    let H := D.N_det
    exact PrimitiveCarrierInvariant H D.determinantProfile ∧
      PrimitiveCarrierFactorsThroughQuotient H D.determinantProfile ∧
      PrimitiveCarrierSupportOnQuotient H D.active D.channel

/-- Any other quotient preserves the same determinant profile iff its kernel sits inside `N_det`. -/
def preservation_criterion (D : conclusion_artin_determinant_minimal_visible_quotient_data) : Prop :=
  by
    letI := D.instCommGroupG
    exact ∀ K : Subgroup D.G, PrimitiveCarrierInvariant K D.determinantProfile ↔ K ≤ D.N_det

/-- `N_det` is the unique minimal quotient kernel preserving the determinant profile. -/
def unique_minimality (D : conclusion_artin_determinant_minimal_visible_quotient_data) : Prop :=
  by
    letI := D.instCommGroupG
    exact ∀ K : Subgroup D.G,
      PrimitiveCarrierInvariant K D.determinantProfile → D.N_det ≤ K → K = D.N_det

end conclusion_artin_determinant_minimal_visible_quotient_data

open conclusion_artin_determinant_minimal_visible_quotient_data

/-- Paper label: `thm:conclusion-artin-determinant-minimal-visible-quotient`. The kernel obtained
by intersecting the determinant-active channels is exactly the maximal subgroup on which the
determinant profile is constant, so quotienting by it preserves precisely the active determinant
factors and is uniquely minimal among determinant-preserving quotients. -/
theorem paper_conclusion_artin_determinant_minimal_visible_quotient
    (D : conclusion_artin_determinant_minimal_visible_quotient_data) :
    D.minimal_quotient_preserves_determinant ∧ D.preservation_criterion ∧ D.unique_minimality := by
  letI := D.instFintypeG
  letI := D.instCommGroupG
  rcases paper_conclusion_primitive_minimal_carrier_quotient D.active D.channel D.coeff
      D.determinantProfile D.channel_one D.channel_mul D.determinant_expansion
      D.coeff_detects_kernel with ⟨hInv, hFactors, hMax, hSupport⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold conclusion_artin_determinant_minimal_visible_quotient_data.minimal_quotient_preserves_determinant
    exact ⟨hInv, hFactors, hSupport⟩
  · unfold conclusion_artin_determinant_minimal_visible_quotient_data.preservation_criterion
    intro K
    constructor
    · intro hK
      exact hMax K hK
    · intro hK c h hh
      exact hInv c h (hK hh)
  · unfold conclusion_artin_determinant_minimal_visible_quotient_data.unique_minimality
    intro K hK hNK
    exact le_antisymm (hMax K hK) hNK

end Omega.Conclusion
