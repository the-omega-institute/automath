import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-bartholdi-tropical-mass-conservation`. -/
theorem paper_conclusion_realinput40_bartholdi_tropical_mass_conservation :
    ((2 : Rat) * 1 + 12 * (1 / 2 : Rat) + 3 * (1 / 3 : Rat) = 9) ∧
      (forall t : Int,
        (-t ^ 2) * (t ^ 2 * (1 - t) ^ 2) * (-4 * t ^ 2 * (t - 1) ^ 7) =
          4 * t ^ 6 * (t - 1) ^ 9) := by
  constructor
  · norm_num
  · intro t
    ring

end Omega.Conclusion
