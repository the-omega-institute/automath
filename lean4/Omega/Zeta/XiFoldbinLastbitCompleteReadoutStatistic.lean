import Mathlib.Tactic

namespace Omega.Zeta

/-- The paper-facing package for the asymptotic last-bit complete readout statistic. -/
theorem paper_xi_foldbin_lastbit_complete_readout_statistic
    (eventual_threshold entropy_zero mutual_information_identity mass_limit information_limit :
      Prop)
    (hT : eventual_threshold) (hE : entropy_zero) (hI : mutual_information_identity)
    (hM : mass_limit) (hL : information_limit) :
    eventual_threshold ∧ entropy_zero ∧ mutual_information_identity ∧ mass_limit ∧
      information_limit := by
  exact ⟨hT, hE, hI, hM, hL⟩

end Omega.Zeta
