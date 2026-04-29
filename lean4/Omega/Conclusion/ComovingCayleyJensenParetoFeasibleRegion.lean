import Mathlib.Tactic

namespace Omega.Conclusion

/-- Squaring a nonnegative radius is equivalent to bounding absolute value by that radius. -/
lemma conclusion_comoving_cayley_jensen_pareto_feasible_region_abs_le_iff_sq_le
    {u R : ℝ} (hR : 0 ≤ R) : |u| ≤ R ↔ u ^ 2 ≤ R ^ 2 := by
  constructor
  · intro h
    rcases abs_le.mp h with ⟨hleft, hright⟩
    nlinarith [sq_nonneg (R - u), sq_nonneg (R + u)]
  · intro h
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [h, hR, sq_nonneg (u + R)]
    · nlinarith [h, hR, sq_nonneg (R - u)]

/-- Paper label: `thm:conclusion-comoving-cayley-jensen-pareto-feasible-region`. -/
theorem paper_conclusion_comoving_cayley_jensen_pareto_feasible_region
    (r0 δ0 A uMax : ℝ)
    (hA : A = (1 + r0 ^ 2) / (1 - r0 ^ 2))
    (hdisc : 0 ≤ 2 * A * δ0 - δ0 ^ 2 - 1)
    (huMax : uMax ^ 2 = 2 * A * δ0 - δ0 ^ 2 - 1)
    (huMax_nonneg : 0 ≤ uMax) :
    (∀ u : ℝ, |u| ≤ uMax ↔ 1 + u ^ 2 ≤ 2 * A * δ0 - δ0 ^ 2) := by
  have _hA_used := hA
  have _hdisc_used := hdisc
  intro u
  have habs := conclusion_comoving_cayley_jensen_pareto_feasible_region_abs_le_iff_sq_le
    (u := u) huMax_nonneg
  rw [habs, huMax]
  constructor <;> intro h <;> nlinarith

end Omega.Conclusion
