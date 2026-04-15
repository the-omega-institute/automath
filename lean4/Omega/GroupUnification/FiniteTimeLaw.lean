import Omega.GroupUnification.ExactClock

namespace Omega.GroupUnification

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the endpoint-law and finite-time-variance corollary in
    `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    cor:finite-time-law -/
theorem paper_zero_jitter_finite_time_law
    (exactClock endpointLaw finiteTimeVariance boundedVariance asymptoticVariance : Prop)
    (hEndpoint : exactClock → endpointLaw)
    (hVariance : endpointLaw → finiteTimeVariance)
    (hBounded : finiteTimeVariance → boundedVariance)
    (hAsymptotic : finiteTimeVariance → asymptoticVariance) :
    exactClock →
      endpointLaw ∧ finiteTimeVariance ∧ boundedVariance ∧ asymptoticVariance := by
  intro hExactClock
  have hEndpointLaw : endpointLaw := hEndpoint hExactClock
  have hFiniteVariance : finiteTimeVariance := hVariance hEndpointLaw
  exact
    ⟨hEndpointLaw, hFiniteVariance, hBounded hFiniteVariance, hAsymptotic hFiniteVariance⟩

end Omega.GroupUnification
