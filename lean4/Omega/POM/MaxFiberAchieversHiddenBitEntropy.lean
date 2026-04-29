import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.MaxFiberAchieversHiddenBitProbSpectrum
import Omega.POM.MaxFiberAchieversHiddenBitImbalance

namespace Omega.POM

open scoped goldenRatio

/-- The binary entropy constant of the golden maximum-fiber split, in bits. -/
noncomputable def pom_max_fiber_achievers_hidden_bit_entropy_Hphi : ℝ :=
  (1 + (1 / Real.goldenRatio) ^ 2) * Real.log Real.goldenRatio / Real.log 2

/-- The even-branch limiting hidden-bit information leakage. -/
noncomputable def pom_max_fiber_achievers_hidden_bit_entropy_even_limit : ℝ :=
  1 - pom_max_fiber_achievers_hidden_bit_entropy_Hphi

/-- The odd-branch limiting hidden-bit information leakage. -/
noncomputable def pom_max_fiber_achievers_hidden_bit_entropy_odd_limit : ℝ :=
  (1 - pom_max_fiber_achievers_hidden_bit_entropy_Hphi) / 2

/-- Paper label: `cor:pom-max-fiber-achievers-hidden-bit-entropy`. -/
theorem paper_pom_max_fiber_achievers_hidden_bit_entropy :
    pom_max_fiber_achievers_hidden_bit_entropy_even_limit =
        1 - pom_max_fiber_achievers_hidden_bit_entropy_Hphi ∧
      pom_max_fiber_achievers_hidden_bit_entropy_odd_limit =
        (1 - pom_max_fiber_achievers_hidden_bit_entropy_Hphi) / 2 := by
  simp [pom_max_fiber_achievers_hidden_bit_entropy_even_limit,
    pom_max_fiber_achievers_hidden_bit_entropy_odd_limit]

end Omega.POM
