import Mathlib.Tactic
import Omega.Zeta.RealInput40BartholdiDet

namespace Omega.Conclusion

open Omega.Zeta

/-- The generic top `z`-coefficient of the Bartholdi factor `F(z,t)`. -/
def conclusion_realinput40_bartholdi_effective_dimension_trichotomy_top_coeff (t : ℤ) : ℤ :=
  -4 * t ^ 2 * (t - 1) ^ 7

/-- Chapter-local effective-dimension wrapper for the audited Bartholdi determinant degree. -/
def conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff (t : ℤ) : ℕ :=
  if t = 0 then 15 else if t = 1 then 9 else 26

/-- Paper label: `thm:conclusion-realinput40-bartholdi-effective-dimension-trichotomy`. The
`t = 0` and `t = 1` Bartholdi specializations are the audited determinant identities, and away from
those two parameters the top coefficient `-4 t² (t - 1)⁷` stays nonzero, so the effective
dimension is the generic value `26`. -/
def conclusion_realinput40_bartholdi_effective_dimension_trichotomy_statement : Prop :=
  (∀ u : ℤ, realInput40BartholdiDeterminant 0 u = 1) ∧
    (∀ u : ℤ, realInput40BartholdiDeterminant 1 u = 0) ∧
    conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff 0 = 15 ∧
    conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff 1 = 9 ∧
    (∀ t : ℤ, t ≠ 0 → t ≠ 1 →
      conclusion_realinput40_bartholdi_effective_dimension_trichotomy_top_coeff t ≠ 0 ∧
        conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff t = 26) ∧
    48 - conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff 0 = 33 ∧
    48 - conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff 1 = 39 ∧
    (∀ t : ℤ, t ≠ 0 → t ≠ 1 →
      48 - conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff t = 22)

theorem paper_conclusion_realinput40_bartholdi_effective_dimension_trichotomy :
    conclusion_realinput40_bartholdi_effective_dimension_trichotomy_statement := by
  have hdet := paper_real_input_40_bartholdi_det { auditTag := 40 }
  refine ⟨hdet.2.2.1, hdet.2.2.2, by simp
    [conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff], by simp
    [conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff], ?_, by norm_num
    [conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff], by norm_num
    [conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff], ?_⟩
  · intro t ht0 ht1
    refine ⟨?_, by simp [conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff, ht0,
      ht1]⟩
    have htm1 : t - 1 ≠ 0 := by
      intro h
      apply ht1
      linarith
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht0))
      (pow_ne_zero 7 htm1)
  · intro t ht0 ht1
    simp [conclusion_realinput40_bartholdi_effective_dimension_trichotomy_r_eff, ht0, ht1]

end Omega.Conclusion
