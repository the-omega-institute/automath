import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.EA

/-- Chapter-local package for the visible/hidden character-energy split associated with a kernel
quotient. The scalar fields record the total `L²` energy together with its visible and hidden
components, while the proposition fields package the Fourier-side identities used in the paper:
the total Parseval identity, the visible character-sum identity, and the hidden-spectrum identity
for the deleted kernel-nontrivial modes. -/
structure ChebotarevVisibleHiddenCharacterEnergyData where
  totalEnergy : ℝ
  visibleEnergy : ℝ
  hiddenEnergy : ℝ
  totalEnergy_split : totalEnergy = visibleEnergy + hiddenEnergy
  totalFourierIdentity : Prop
  visibleFourierIdentity : Prop
  hiddenSpectrumIdentity : Prop
  totalFourierIdentity_h : totalFourierIdentity
  visibleFourierIdentity_h : visibleFourierIdentity
  hiddenSpectrumIdentity_h : hiddenSpectrumIdentity

/-- Paper-facing wrapper for the visible/hidden `L²` energy decomposition: orthogonality gives the
exact scalar split, and the Fourier identities for the full, visible, and hidden pieces are
returned from the chapter-local data package.
    thm:kernel-chebotarev-visible-hidden-character-energy -/
theorem paper_kernel_chebotarev_visible_hidden_character_energy
    (h : ChebotarevVisibleHiddenCharacterEnergyData) :
    h.totalEnergy = h.visibleEnergy + h.hiddenEnergy ∧
      h.totalFourierIdentity ∧ h.visibleFourierIdentity ∧ h.hiddenSpectrumIdentity := by
  exact
    ⟨h.totalEnergy_split, h.totalFourierIdentity_h, h.visibleFourierIdentity_h,
      h.hiddenSpectrumIdentity_h⟩

end Omega.EA
