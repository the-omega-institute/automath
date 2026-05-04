import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-ambiguity-shell-periodic-modulation-pole-star-equivalence`. -/
theorem paper_conclusion_ambiguity_shell_periodic_modulation_pole_star_equivalence
    (periodicModulation poleStar imprimitive : Prop)
    (hcoeff : periodicModulation ↔ poleStar) (hpf : poleStar ↔ imprimitive) :
    (periodicModulation ↔ poleStar) ∧
      (poleStar ↔ imprimitive) ∧ (periodicModulation ↔ imprimitive) := by
  exact ⟨hcoeff, hpf, hcoeff.trans hpf⟩

end Omega.Conclusion
