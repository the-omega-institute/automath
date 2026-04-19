import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.GroupUnification.ParryCommutingSquarePhi

/-- The local commuting-square relation forces the golden-ratio transition weights.
    prop:parry-commuting-square-gives-phi -/
theorem paper_parry_commuting_square_gives_phi_seeds {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hcomm : a ^ 2 = 1 - a) :
    a = Real.goldenRatio⁻¹ ∧ 1 - a = Real.goldenRatio⁻¹ ^ 2 := by
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsq : (2 * a + 1) ^ 2 = (Real.sqrt 5) ^ 2 := by
    nlinarith [hcomm, hsqrt5_sq]
  have hsqrt5_pos : 0 < Real.sqrt 5 := by
    positivity
  have hapos : 0 < 2 * a + 1 := by
    nlinarith
  have hroot : 2 * a + 1 = Real.sqrt 5 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hEq | hEq
    · exact hEq
    · exfalso
      linarith
  have ha : a = Real.goldenRatio⁻¹ := by
    rw [Real.inv_goldenRatio, Real.goldenConj]
    nlinarith
  have hone : 1 - a = Real.goldenRatio⁻¹ ^ 2 := by
    rw [ha]
    field_simp [show Real.goldenRatio ≠ 0 by positivity]
    nlinarith [Real.goldenRatio_sq]
  exact ⟨ha, hone⟩

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_parry_commuting_square_gives_phi_package {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hcomm : a ^ 2 = 1 - a) :
    a = Real.goldenRatio⁻¹ ∧ 1 - a = Real.goldenRatio⁻¹ ^ 2 :=
  paper_parry_commuting_square_gives_phi_seeds ha0 ha1 hcomm

/-- Paper-facing wrapper matching the exact proposition label. -/
theorem paper_parry_commuting_square_gives_phi {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hcomm : a ^ 2 = 1 - a) :
    a = Real.goldenRatio⁻¹ ∧ 1 - a = Real.goldenRatio⁻¹ ^ 2 :=
  paper_parry_commuting_square_gives_phi_seeds ha0 ha1 hcomm

end Omega.GroupUnification.ParryCommutingSquarePhi
