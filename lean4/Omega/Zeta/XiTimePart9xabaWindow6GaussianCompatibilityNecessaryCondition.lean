import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label:
`prop:xi-time-part9xaba-window6-gaussian-compatibility-necessary-condition`. -/
theorem paper_xi_time_part9xaba_window6_gaussian_compatibility_necessary_condition
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℝ) (b c3 : ℝ) (hb : b ≠ 0)
    (hc3 : c3 ≠ 0)
    (hcum3_zero :
      c3 / b ^ 3 * (∑ x : ι, if d x = 3 then a x ^ 3 else 0) = 0) :
    (∑ x : ι, if d x = 3 then a x ^ 3 else 0) / b ^ 3 = 0 := by
  have hb3 : b ^ 3 ≠ 0 := pow_ne_zero 3 hb
  have hfactor : c3 / b ^ 3 ≠ 0 := div_ne_zero hc3 hb3
  have hsum : (∑ x : ι, if d x = 3 then a x ^ 3 else 0) = 0 := by
    rcases mul_eq_zero.mp hcum3_zero with h | h
    · exact False.elim (hfactor h)
    · exact h
  simp [hsum]

end Omega.Zeta
