import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-window6-spin1-cartan-shadow`. -/
theorem paper_conclusion_window6_spin1_cartan_shadow (lam : ℝ) :
    (lam - 1) * (lam - 3) * (lam - 5) =
      8 * (((lam - 3) / 2 - 1) * ((lam - 3) / 2) * ((lam - 3) / 2 + 1)) := by
  ring_nf

end Omega.Conclusion
