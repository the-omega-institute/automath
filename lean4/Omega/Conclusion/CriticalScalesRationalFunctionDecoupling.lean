import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete field-intersection package for the critical-scale rational-function decoupling.
The generated-field carriers are represented by subsets of `ℝ`; the audited facts say that the
`u_R`/`u_{LY}` intersection is exactly the rational copy of `ℚ`, and that the `b`-field is the
same generated field as `u_{LY}`. -/
structure conclusion_critical_scales_rational_function_decoupling_data where
  uRField : Set ℝ
  uLYField : Set ℝ
  bField : Set ℝ
  uR_inter_uLY_eq_rational :
    uRField ∩ uLYField = Set.range fun q : ℚ => (q : ℝ)
  bField_eq_uLYField : bField = uLYField

namespace conclusion_critical_scales_rational_function_decoupling_data

/-- Every rational-function value lying in both the `u_R` and `u_{LY}` generated fields is
rational. -/
def uR_uLY_common_values_rational
    (D : conclusion_critical_scales_rational_function_decoupling_data) : Prop :=
  ∀ x : ℝ, x ∈ D.uRField → x ∈ D.uLYField → ∃ q : ℚ, (q : ℝ) = x

/-- Every rational-function value lying in both the `u_R` and `b` generated fields is rational. -/
def uR_b_common_values_rational
    (D : conclusion_critical_scales_rational_function_decoupling_data) : Prop :=
  ∀ x : ℝ, x ∈ D.uRField → x ∈ D.bField → ∃ q : ℚ, (q : ℝ) = x

end conclusion_critical_scales_rational_function_decoupling_data

open conclusion_critical_scales_rational_function_decoupling_data

/-- Paper label: `thm:conclusion-critical-scales-rational-function-decoupling`. -/
theorem paper_conclusion_critical_scales_rational_function_decoupling
    (D : conclusion_critical_scales_rational_function_decoupling_data) :
    D.uR_uLY_common_values_rational ∧ D.uR_b_common_values_rational := by
  refine ⟨?_, ?_⟩
  · intro x hxR hxLY
    have hx : x ∈ D.uRField ∩ D.uLYField := ⟨hxR, hxLY⟩
    rcases (show x ∈ Set.range (fun q : ℚ => (q : ℝ)) from
      D.uR_inter_uLY_eq_rational ▸ hx) with ⟨q, hq⟩
    exact ⟨q, hq⟩
  · intro x hxR hxb
    have hxLY : x ∈ D.uLYField := by
      simpa [D.bField_eq_uLYField] using hxb
    have hx : x ∈ D.uRField ∩ D.uLYField := ⟨hxR, hxLY⟩
    rcases (show x ∈ Set.range (fun q : ℚ => (q : ℝ)) from
      D.uR_inter_uLY_eq_rational ▸ hx) with ⟨q, hq⟩
    exact ⟨q, hq⟩

end Omega.Conclusion
