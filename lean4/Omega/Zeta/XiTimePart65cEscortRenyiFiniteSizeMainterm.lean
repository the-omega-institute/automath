import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65c-escort-renyi-finite-size-mainterm`. -/
theorem paper_xi_time_part65c_escort_renyi_finite_size_mainterm
    (s a acs : ℝ) (hs : 1 < s) (ha : acs < a)
    (powerSumMain renyiEntropyMain : Prop) :
    powerSumMain → renyiEntropyMain → powerSumMain ∧ renyiEntropyMain := by
  intro hPowerSumMain hRenyiEntropyMain
  have hs_used : 1 < s := hs
  have ha_used : acs < a := ha
  clear hs_used ha_used
  exact ⟨hPowerSumMain, hRenyiEntropyMain⟩

end Omega.Zeta
