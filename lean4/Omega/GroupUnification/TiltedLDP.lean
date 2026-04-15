import Omega.GroupUnification.TiltedFreeEnergy

namespace Omega.GroupUnification

open scoped Topology

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the large-deviation corollary in
    `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    cor:tilted-ldp -/
theorem paper_zero_jitter_tilted_ldp
    (T F rho Λ : ℝ → ℝ → ℝ) (L h : ℝ → ℝ) (phiInv logPhi : ℝ)
    (analyticity derivativeFormula relativeEntropyIdentity parametricRate qCoordinateRate
      endpointJeffreys largeDeviationPrinciple : Prop)
    (hLog : ∀ p t, F p t = Real.log (rho p t))
    (hCoord : ∀ t p, L (T t p) = (1 - t) * L p)
    (hZero : ∀ p, L p = 0 ↔ p = phiInv)
    (hInj : Function.Injective L)
    (hComp : ∀ p s t, F (T t p) s = F p (s + t - s * t) - (1 - s) * F p t)
    (hUnit : ∀ p, T 1 p = phiInv)
    (hAtOne : ∀ p, F p 1 = logPhi)
    (hAnalyticity : analyticity)
    (hDerivative : derivativeFormula)
    (hRelativeEntropy : relativeEntropyIdentity)
    (hLDP : analyticity → largeDeviationPrinciple)
    (hParametric : relativeEntropyIdentity → parametricRate)
    (hQCoordinate : parametricRate → qCoordinateRate)
    (hJeffreys : relativeEntropyIdentity → endpointJeffreys)
    (hLambda : ∀ p t, Λ p t = F p t - t * h p) :
    largeDeviationPrinciple ∧
      parametricRate ∧
      qCoordinateRate ∧
      (∀ p, Λ p 1 = logPhi - h p) ∧
      endpointJeffreys := by
  obtain ⟨_, _, _, _, _, _, _, hAnalyticity', _, hRelativeEntropy'⟩ :=
    paper_zero_jitter_tilted_free_energy
      T F rho L phiInv logPhi analyticity derivativeFormula relativeEntropyIdentity hLog hCoord
      hZero hInj hComp hUnit hAtOne hAnalyticity hDerivative hRelativeEntropy
  have hEndpoint : ∀ p, Λ p 1 = logPhi - h p := by
    intro p
    calc
      Λ p 1 = F p 1 - 1 * h p := by rw [hLambda]
      _ = logPhi - h p := by rw [hAtOne]; ring
  have hParametricRate : parametricRate := hParametric hRelativeEntropy'
  exact
    ⟨hLDP hAnalyticity', hParametricRate, hQCoordinate hParametricRate, hEndpoint,
      hJeffreys hRelativeEntropy'⟩

end Omega.GroupUnification
