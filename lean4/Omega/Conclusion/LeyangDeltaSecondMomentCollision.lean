import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The Leyang fiber-deviation second moment obtained from the self-fiber product point count. -/
def leyangDeltaSecondMoment (D ram aE : ℝ) : ℝ :=
  D - ram + aE

/-- Normalized second moment `(1 / p) ∑ δ_p(y)^2`. -/
noncomputable def leyangNormalizedSecondMoment (p D ram aE : ℝ) : ℝ :=
  leyangDeltaSecondMoment D ram aE / p

/-- The collision-probability main term appearing in the paper. -/
noncomputable def leyangCollisionMainTerm (p : ℝ) : ℝ :=
  2 / p

/-- Paper-facing second-moment/collision package: the self-fiber-product identity expands to
`D - ram + a_E`, the Hasse-Weil error terms yield the explicit `14 / √p + c₁ / p` control on the
normalized second moment, and the leading collision term is `2 / p`.
    cor:conclusion-leyang-delta-second-moment-collision -/
theorem paper_conclusion_leyang_delta_second_moment_collision
    (p D ram aE c1 : ℝ) (hp : 0 < p) (hD : |D - (p + 1)| ≤ 12 * Real.sqrt p)
    (hRam : |1 - ram| ≤ c1) (haE : |aE| ≤ 2 * Real.sqrt p) :
    leyangDeltaSecondMoment D ram aE = D - ram + aE ∧
      |leyangNormalizedSecondMoment p D ram aE - 1| ≤ 14 / Real.sqrt p + c1 / p ∧
      leyangCollisionMainTerm p = 2 / p := by
  have hp_ne : p ≠ 0 := by positivity
  have hsqrt_pos : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsqrt_ne : Real.sqrt p ≠ 0 := hsqrt_pos.ne'
  have hdelta_sub :
      leyangDeltaSecondMoment D ram aE - p = (D - (p + 1)) + (1 - ram) + aE := by
    unfold leyangDeltaSecondMoment
    ring
  have htriangle :
      |leyangDeltaSecondMoment D ram aE - p| ≤ 14 * Real.sqrt p + c1 := by
    rw [hdelta_sub]
    have h_outer :
        |(D - (p + 1)) + ((1 - ram) + aE)| ≤ |D - (p + 1)| + |(1 - ram) + aE| := by
      simpa using abs_add_le (D - (p + 1)) ((1 - ram) + aE)
    have h_inner : |(1 - ram) + aE| ≤ |1 - ram| + |aE| := by
      simpa using abs_add_le (1 - ram) aE
    calc
      |(D - (p + 1)) + (1 - ram) + aE|
          ≤ |D - (p + 1)| + |1 - ram| + |aE| := by
            simpa [add_assoc] using le_trans h_outer (by nlinarith [h_inner])
      _ ≤ 12 * Real.sqrt p + c1 + 2 * Real.sqrt p := by linarith
      _ = 14 * Real.sqrt p + c1 := by ring
  have hnorm_eq :
      |leyangNormalizedSecondMoment p D ram aE - 1| =
        |leyangDeltaSecondMoment D ram aE - p| / p := by
    unfold leyangNormalizedSecondMoment
    have hfrac :
        leyangDeltaSecondMoment D ram aE / p - 1 =
          (leyangDeltaSecondMoment D ram aE - p) / p := by
      field_simp [hp_ne]
    rw [hfrac, abs_div, abs_of_pos hp]
  have hdiv :
      |leyangDeltaSecondMoment D ram aE - p| / p ≤ (14 * Real.sqrt p + c1) / p := by
    exact div_le_div_of_nonneg_right htriangle hp.le
  have hrewrite :
      (14 * Real.sqrt p + c1) / p = 14 / Real.sqrt p + c1 / p := by
    field_simp [hp_ne, hsqrt_ne]
    nlinarith [Real.sq_sqrt (le_of_lt hp)]
  refine ⟨rfl, ?_, rfl⟩
  rw [hnorm_eq]
  calc
    |leyangDeltaSecondMoment D ram aE - p| / p ≤ (14 * Real.sqrt p + c1) / p := hdiv
    _ = 14 / Real.sqrt p + c1 / p := hrewrite

end Omega.Conclusion
