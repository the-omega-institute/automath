import Omega.Folding.PhiSubshiftFactor

namespace Omega.Folding

/-- Concrete data for restricting the sliding block code `Φ_m` to a shift-invariant source
subshift. -/
structure phi_m_factor_on_subshift_data where
  A : Type*
  B : Type*
  m : ℕ
  localRule : (Fin m → A) → B
  sourceSubshift : Set (ℤ → A)
  source_shiftInvariant : ShiftInvariant sourceSubshift

namespace phi_m_factor_on_subshift_data

/-- The image subshift obtained from the restricted `Φ_m` map. -/
def imageSubshift (D : phi_m_factor_on_subshift_data) : Set (ℤ → D.B) :=
  slideBlockCode D.m D.localRule '' D.sourceSubshift

/-- A concrete continuity witness for `Φ_m`: the value at coordinate `0` depends only on the
window `0, ..., m - 1`. -/
def restrict_continuous (D : phi_m_factor_on_subshift_data) : Prop :=
  ∀ s t : ℤ → D.A, (∀ i : Fin D.m, s i.val = t i.val) →
    slideBlockCode D.m D.localRule s 0 = slideBlockCode D.m D.localRule t 0

/-- The restricted map still commutes with the shift. -/
def restrict_shift_commutes (D : phi_m_factor_on_subshift_data) : Prop :=
  ∀ s : ℤ → D.A, s ∈ D.sourceSubshift →
    slideBlockCode D.m D.localRule (shiftSeq s) = shiftSeq (slideBlockCode D.m D.localRule s)

/-- The image of the restricted map is a subshift. -/
def image_is_subshift (D : phi_m_factor_on_subshift_data) : Prop :=
  ShiftInvariant D.imageSubshift

/-- The restricted map factors onto its image by the tautological surjection onto that image. -/
def restrict_factors_onto_image (D : phi_m_factor_on_subshift_data) : Prop :=
  ∀ t ∈ D.imageSubshift, ∃ s ∈ D.sourceSubshift, slideBlockCode D.m D.localRule s = t

end phi_m_factor_on_subshift_data

open phi_m_factor_on_subshift_data

/-- Paper label: `prop:Phi_m-factor-on-subshift`. The sliding block code `Φ_m` remains a local
continuous, shift-commuting map on every source subshift, its image is again shift invariant, and
the restricted map is a factor onto that image. -/
theorem paper_phi_m_factor_on_subshift (D : phi_m_factor_on_subshift_data) :
    D.restrict_continuous ∧ D.restrict_shift_commutes ∧ D.image_is_subshift ∧
      D.restrict_factors_onto_image := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t hwindow
    simp [slideBlockCode]
    congr
    funext i
    exact hwindow i
  · intro s hs
    exact slideBlockCode_restriction_equivariant D.m D.localRule D.sourceSubshift
      D.source_shiftInvariant s hs
  · exact slideBlockCode_image_shiftInvariant D.m D.localRule D.sourceSubshift
      D.source_shiftInvariant
  · exact slideBlockCode_restrict_surjective D.m D.localRule D.sourceSubshift

end Omega.Folding
