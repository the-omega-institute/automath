/-- Paper-facing wrapper for the large-coupling implication yielding the discriminant
    speed power-law conclusion.
    thm:conclusion-rankone-large-coupling-discriminant-speed-powerlaw -/
theorem paper_conclusion_rankone_large_coupling_discriminant_speed_powerlaw
    (largeCoupling discriminantPowerLaw : Prop)
    (h : largeCoupling -> discriminantPowerLaw) : largeCoupling -> discriminantPowerLaw := by
  exact h
