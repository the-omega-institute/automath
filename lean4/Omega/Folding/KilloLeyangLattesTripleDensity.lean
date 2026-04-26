import Mathlib.Tactic
import Omega.Folding.KilloLeyangJointDensityExplicit

namespace Omega.Folding

/-- Paper label: `cor:killo-leyang-lattes-triple-density`. -/
theorem paper_killo_leyang_lattes_triple_density :
    ((1 : ℚ) / Nat.factorial 10) * (1 / 6 : ℚ) * (1 / 48 : ℚ) =
      1 / (Nat.factorial 10 * 6 * 48 : ℚ) ∧
      ((28319 : ℚ) / 44800) * (1 / 6 : ℚ) * (1 / 48 : ℚ) = 28319 / 12902400 := by
  constructor
  · norm_num [Nat.factorial]
  · have hjoint : ((28319 : ℚ) / 44800) * (1 / 6 : ℚ) = 28319 / 268800 :=
      paper_killo_leyang_joint_density_explicit.1
    have hjoint' :
        ((28319 : ℚ) / 44800) * (1 / 6 : ℚ) * (1 / 48 : ℚ) =
          (28319 / 268800 : ℚ) * (1 / 48 : ℚ) := by
      exact congrArg (fun q : ℚ => q * (1 / 48 : ℚ)) hjoint
    rw [hjoint']
    norm_num

end Omega.Folding
