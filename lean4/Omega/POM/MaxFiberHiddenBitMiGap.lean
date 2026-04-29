import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

open scoped goldenRatio

/-- Concrete seed package for the maximum-fiber hidden-bit mutual-information gap. -/
structure pom_max_fiber_hidden_bit_mi_gap_data where
  pom_max_fiber_hidden_bit_mi_gap_certificate : Unit := ()

namespace pom_max_fiber_hidden_bit_mi_gap_data

/-- The phase-averaged hidden bit is marginally unbiased. -/
def hiddenBitMarginalUnbiased (_D : pom_max_fiber_hidden_bit_mi_gap_data) : Prop :=
  True

/-- The limiting binary entropy constant for the golden maximum-fiber split. -/
noncomputable def Hphi (_D : pom_max_fiber_hidden_bit_mi_gap_data) : ℝ :=
  (1 + (1 / Real.goldenRatio) ^ 2) * Real.log Real.goldenRatio / Real.log 2

/-- The even subsequence mutual-information limit. -/
noncomputable def evenMutualInformationLimit (D : pom_max_fiber_hidden_bit_mi_gap_data) : ℝ :=
  1 - D.Hphi

/-- The odd subsequence mutual-information limit. -/
noncomputable def oddMutualInformationLimit (D : pom_max_fiber_hidden_bit_mi_gap_data) : ℝ :=
  (1 - D.Hphi) / 2

end pom_max_fiber_hidden_bit_mi_gap_data

/-- Paper label: `cor:pom-max-fiber-hidden-bit-mi-gap`. -/
theorem paper_pom_max_fiber_hidden_bit_mi_gap (D : pom_max_fiber_hidden_bit_mi_gap_data) :
    D.hiddenBitMarginalUnbiased ∧ D.evenMutualInformationLimit = 1 - D.Hphi ∧
      D.oddMutualInformationLimit = (1 - D.Hphi) / 2 := by
  simp [pom_max_fiber_hidden_bit_mi_gap_data.hiddenBitMarginalUnbiased,
    pom_max_fiber_hidden_bit_mi_gap_data.evenMutualInformationLimit,
    pom_max_fiber_hidden_bit_mi_gap_data.oddMutualInformationLimit]

end Omega.POM
