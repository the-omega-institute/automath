import Omega.Folding.Entropy

open Filter Topology

namespace Omega.POM

/-- Paper-facing wrapper for the finite hidden-bit density estimate and its limiting density.
    Paper label: `cor:pom-hidden-bit-entropy`. -/
theorem paper_pom_hidden_bit_entropy :
    (∀ m : Nat, 3 * Omega.hiddenBitCount m ≤ 2 ^ m ∧
      2 ^ m ≤ 3 * Omega.hiddenBitCount m + 2) ∧
      Tendsto (fun m => (Omega.hiddenBitCount m : ℝ) / 2 ^ m) atTop (nhds (1 / 3)) := by
  constructor
  · intro m
    exact Omega.hiddenBitCount_near_third m
  · exact Omega.Entropy.hiddenBitDensity_tendsto_third

end Omega.POM
