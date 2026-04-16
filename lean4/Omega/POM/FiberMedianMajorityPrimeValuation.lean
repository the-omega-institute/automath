import Mathlib.Tactic

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the coordinatewise median and prime-valuation majority package.
    thm:pom-fiber-median-majority-prime-valuation -/
theorem paper_pom_fiber_median_majority_prime_valuation
    (thetaPrimeIsometry coordinatewiseMedian majorityValuationIdentity : Prop)
    (hIso : thetaPrimeIsometry) (hMedian : thetaPrimeIsometry -> coordinatewiseMedian)
    (hMaj : coordinatewiseMedian -> majorityValuationIdentity) :
    thetaPrimeIsometry ∧ coordinatewiseMedian ∧ majorityValuationIdentity := by
  refine ⟨hIso, hMedian hIso, ?_⟩
  exact hMaj (hMedian hIso)

end Omega.POM
