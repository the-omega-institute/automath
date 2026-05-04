import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zeckendorf-ambiguity-shell-pole-star-collapse`.
Once the finite-plane pole certificate is excluded, pole-star and periodic-modulation
exclusions follow by the supplied implication chain. -/
theorem paper_conclusion_zeckendorf_ambiguity_shell_pole_star_collapse
    (m : ℕ) (hm : 3 ≤ m)
    (hasFinitePlanePole hasPoleStar hasPeriodicModulation : Prop)
    (hNoPole : ¬ hasFinitePlanePole)
    (hStarImpliesPole : hasPoleStar → hasFinitePlanePole)
    (hPeriodicImpliesStar : hasPeriodicModulation → hasPoleStar) :
    ¬ hasFinitePlanePole ∧ ¬ hasPoleStar ∧ ¬ hasPeriodicModulation := by
  have _zeckendorfRange : 3 ≤ m := hm
  refine ⟨hNoPole, ?_, ?_⟩
  · intro hStar
    exact hNoPole (hStarImpliesPole hStar)
  · intro hPeriodic
    exact hNoPole (hStarImpliesPole (hPeriodicImpliesStar hPeriodic))

end Omega.Conclusion
