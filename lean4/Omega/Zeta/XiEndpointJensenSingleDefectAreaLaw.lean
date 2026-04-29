import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The explicit one-defect endpoint Jensen area law written in the absolute-value form from the
paper. The parameter `gamma` drops out after translating the integration variable. -/
noncomputable def xi_endpoint_jensen_single_defect_area (beta _gamma : Real) : Real :=
  let δ := 1 / 2 - beta
  Real.pi * ((1 + δ) - |1 - δ|)

theorem paper_xi_endpoint_jensen_single_defect_area_law
    (beta gamma : Real) (hbeta : beta < 1 / 2) :
    xi_endpoint_jensen_single_defect_area beta gamma = 2 * Real.pi * min (1 / 2 - beta) 1 := by
  dsimp [xi_endpoint_jensen_single_defect_area]
  set δ : Real := 1 / 2 - beta
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  by_cases hδle : δ ≤ 1
  · have habs : |1 - δ| = 1 - δ := abs_of_nonneg (sub_nonneg.mpr hδle)
    rw [habs, min_eq_left hδle]
    ring
  · have hδgt : 1 < δ := lt_of_not_ge hδle
    have habs : |1 - δ| = δ - 1 := by
      rw [abs_of_neg]
      · ring
      · linarith
    rw [habs, min_eq_right (le_of_lt hδgt)]
    ring

end Omega.Zeta
