import Omega.Folding.MaxFiberTwoStep

namespace Omega.POM

/-- Paper-facing wrapper for the hidden-bit count closed form.
    `thm:pom-hidden-bit-count` -/
theorem paper_pom_hidden_bit_count (m : Nat) : Omega.hiddenBitCount m = 2 ^ m / 3 := by
  simpa using Omega.hiddenBitCount_floor_div_three m

end Omega.POM
