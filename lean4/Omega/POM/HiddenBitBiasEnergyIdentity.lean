import Mathlib.Tactic
import Omega.POM.HiddenBitJumpCollisionIsomorphism

namespace Omega.POM

/-- Paper label: `thm:pom-hiddenbit-bias-energy-identity`. The integer-valued bias-energy
identity is already established in the collision decomposition package; this theorem registers the
paper-facing POM name for that exact statement. -/
theorem paper_pom_hiddenbit_bias_energy_identity (m : ℕ) :
    (∑ x : X (m + 2), (((fiberHiddenBitCount 0 x : ℤ) - (fiberHiddenBitCount 1 x : ℤ)) ^ 2)) =
      (momentSum 2 (m + 2) : ℤ) - 4 * (momentSum 2 m : ℤ) := by
  simpa using (Omega.hiddenBitBiasEnergy_int m)

end Omega.POM
