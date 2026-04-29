import Omega.Zeta.XiAbelianBlockToeplitzDirectsum
import Omega.Zeta.XiAbelianChannelKappaCarAdditivity
import Omega.Zeta.AbelianChannelNegativityLocalization

namespace Omega.Zeta

/-- Paper label: `prop:xi-abelian-single-channel-localization-and-pencil-union`. -/
theorem paper_xi_abelian_single_channel_localization_and_pencil_union
    {ι Candidate : Type*} [Fintype ι] (neg : ι -> Nat)
    (channelMultiplicity : ι -> Candidate -> Nat) (blockMultiplicity : Candidate -> Nat)
    (hneg : 0 < Finset.univ.sum neg)
    (hspectrum :
      forall c, blockMultiplicity c = Finset.univ.sum (fun chi => channelMultiplicity chi c)) :
    (Exists fun chi => 0 < neg chi) ∧
      (forall c, blockMultiplicity c = Finset.univ.sum (fun chi => channelMultiplicity chi c)) := by
  exact ⟨paper_xi_abelian_channel_negativity_localization neg hneg, hspectrum⟩

end Omega.Zeta
