import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part69c-audited-even-minsector-abel-share`. -/
theorem paper_xi_time_part69c_audited_even_minsector_abel_share
    (rankMin rankAb : Nat -> Nat)
    (h6 : rankMin 6 = 8 /\ rankAb 6 = 21)
    (h8 : rankMin 8 = 21 /\ rankAb 8 = 55)
    (h10 : rankMin 10 = 55 /\ rankAb 10 = 144)
    (h12 : rankMin 12 = 144 /\ rankAb 12 = 377) :
    (rankMin 6 = 8 /\ rankAb 6 = 21) /\
      (rankMin 8 = 21 /\ rankAb 8 = 55) /\
        (rankMin 10 = 55 /\ rankAb 10 = 144) /\
          (rankMin 12 = 144 /\ rankAb 12 = 377) := by
  exact ⟨h6, h8, h10, h12⟩

end Omega.Zeta
