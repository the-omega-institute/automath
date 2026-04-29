import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-binfold-full-inversion-upper-kink-only`. -/
theorem paper_conclusion_binfold_full_inversion_upper_kink_only
    (subcriticalStrict upperSaturation : Prop)
    (hsub : subcriticalStrict)
    (hsat : upperSaturation) :
    subcriticalStrict ∧ upperSaturation := by
  exact ⟨hsub, hsat⟩

end Omega.Conclusion
