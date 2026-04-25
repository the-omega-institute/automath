namespace Omega.Zeta

/-- Paper label: `prop:xi-rightedge-gap-congruence-rank2-certificate`.
Packages the rank-two orbit input, the decaying remainder estimate, and the induced minor and
distance certificates into one theorem-level certificate. -/
theorem paper_xi_rightedge_gap_congruence_rank2_certificate
    (rankTwoOrbit remainderEstimate minorEstimate distanceEstimate : Prop)
    (hOrbit : rankTwoOrbit) (hRem : remainderEstimate)
    (hMinor : rankTwoOrbit → remainderEstimate → minorEstimate)
    (hDist : rankTwoOrbit → remainderEstimate → distanceEstimate) :
    rankTwoOrbit ∧ remainderEstimate ∧ minorEstimate ∧ distanceEstimate := by
  refine ⟨hOrbit, hRem, hMinor hOrbit hRem, hDist hOrbit hRem⟩

end Omega.Zeta
