namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for observation channels as evaluation functionals in
    `2026_circle_dimension_haar_pullback_cauchy_weight_jfa`.
    thm:poisson-channel-rkhs -/
theorem paper_circle_dimension_poisson_channel_rkhs
    (centeredFluctuationProfile profileInL2 secantRepresentation rkhsEvaluation
      originValue identityAtOrigin : Prop)
    (hL2 : centeredFluctuationProfile → profileInL2)
    (hSecant : centeredFluctuationProfile → secantRepresentation)
    (hEval : secantRepresentation → rkhsEvaluation)
    (hOrigin : centeredFluctuationProfile → originValue)
    (hOriginEval : rkhsEvaluation → identityAtOrigin) :
    centeredFluctuationProfile →
      profileInL2 ∧
        secantRepresentation ∧
        rkhsEvaluation ∧
        originValue ∧
        identityAtOrigin := by
  intro hProfile
  have hL2Profile : profileInL2 := hL2 hProfile
  have hSecantRep : secantRepresentation := hSecant hProfile
  have hRKHS : rkhsEvaluation := hEval hSecantRep
  exact ⟨hL2Profile, hSecantRep, hRKHS, hOrigin hProfile, hOriginEval hRKHS⟩

/-- Paper label: `thm:poisson-channel-rkhs`. This is the exact publication-facing wrapper under
    the paper theorem name. -/
theorem paper_poisson_channel_rkhs
    (centeredFluctuationProfile profileInL2 secantRepresentation rkhsEvaluation
      originValue identityAtOrigin : Prop)
    (hL2 : centeredFluctuationProfile -> profileInL2)
    (hSecant : centeredFluctuationProfile -> secantRepresentation)
    (hEval : secantRepresentation -> rkhsEvaluation)
    (hOrigin : centeredFluctuationProfile -> originValue)
    (hOriginEval : rkhsEvaluation -> identityAtOrigin) :
    centeredFluctuationProfile ->
      (profileInL2 ∧ secantRepresentation ∧ rkhsEvaluation ∧ originValue ∧ identityAtOrigin) := by
  intro hProfile
  have hL2Profile : profileInL2 := hL2 hProfile
  have hSecantRep : secantRepresentation := hSecant hProfile
  have hRKHS : rkhsEvaluation := hEval hSecantRep
  exact ⟨hL2Profile, hSecantRep, hRKHS, hOrigin hProfile, hOriginEval hRKHS⟩

end Omega.CircleDimension
