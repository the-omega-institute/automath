import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `lem:pom-s2-hankel-det`. -/
theorem paper_pom_s2_hankel_det :
    (3 * (18 * 110 - 44 * 44) - 7 * (7 * 110 - 44 * 18) +
        18 * (7 * 44 - 18 * 18) : ℤ) = -2 := by
  norm_num

end Omega.POM
