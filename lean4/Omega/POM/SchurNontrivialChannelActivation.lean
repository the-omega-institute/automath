import Omega.POM.SchurPlancherelEnergyIdentity

namespace Omega.POM

open SchurPartitionIndex

noncomputable section

/-- Paper label: `cor:pom-schur-nontrivial-channel-activation`. -/
theorem paper_pom_schur_nontrivial_channel_activation (m : Real) :
    (schurChannelSquareSum m - (schurNormalizedChannelTrace m cycle)^2 > 0 <->
        schurNormalizedChannelTrace m split != 0) /\
      1 <= |schurNormalizedChannelTrace m split / schurDegree split| := by
  constructor
  · rw [schurChannelSquareSum_closed_form, schurNormalizedChannelTrace_cycle,
      schurNormalizedChannelTrace_split]
    constructor
    · intro _h
      norm_num
    · intro _h
      ring_nf
      norm_num
  · rw [schurNormalizedChannelTrace_split]
    norm_num [schurDegree]

end
end Omega.POM
