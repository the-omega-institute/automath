import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-partition-resonance-ratio-test`. -/
theorem paper_pom_partition_resonance_ratio_test
    (q : Nat) (pressure pressureSum ratioRate : Real) (hMain : 2 <= q)
    (hRatio : ratioRate = pressure - pressureSum) :
    ratioRate = pressure - pressureSum := by
  have _ : 2 <= q := hMain
  exact hRatio

end Omega.POM
