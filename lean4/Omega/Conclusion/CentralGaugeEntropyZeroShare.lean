import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-central-gauge-entropy-zero-share`. -/
theorem paper_conclusion_central_gauge_entropy_zero_share
    (deltaS logG : Nat -> Real) (phi C c : Real)
    (hphi_pos : 0 < phi) (hphi_lt : phi < 2) (hC : 0 <= C) (hc : 0 < c)
    (hdeltaS : ∀ᶠ m : Nat in Filter.atTop, 0 <= deltaS m ∧ deltaS m <= C * phi ^ m)
    (hlogG : ∀ᶠ m : Nat in Filter.atTop, c * (m : Real) * 2 ^ m <= logG m)
    (hpos : ∀ᶠ m : Nat in Filter.atTop, 0 < logG m) :
    Filter.Tendsto (fun m : Nat => deltaS m / logG m) Filter.atTop (nhds 0) := by
  let r : Real := phi / 2
  have hr_nonneg : 0 <= r := by
    dsimp [r]
    nlinarith
  have hr_lt_one : r < 1 := by
    dsimp [r]
    nlinarith
  have hgeom :
      Filter.Tendsto (fun m : Nat => (C / c) * r ^ m) Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun m : Nat => r ^ m) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt_one
    simpa using hp.const_mul (C / c)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgeom ?_ ?_
  · filter_upwards [hdeltaS, hpos] with m hS hGpos
    exact div_nonneg hS.1 hGpos.le
  · have hone : ∀ᶠ m : Nat in Filter.atTop, (1 : Real) <= m := by
      exact Filter.eventually_atTop.2 ⟨1, fun m hm => by exact_mod_cast hm⟩
    filter_upwards [hdeltaS, hlogG, hpos, hone] with m hS hG hGpos hm_ge_one
    have hm_pos : 0 < (m : Real) := by
      nlinarith
    have htwo_pow_pos : 0 < (2 : Real) ^ m := pow_pos (by norm_num) m
    have hden_pos : 0 < c * (m : Real) * 2 ^ m := by
      positivity
    have hnum_bound_nonneg : 0 <= C * phi ^ m := le_trans hS.1 hS.2
    calc
      deltaS m / logG m <= (C * phi ^ m) / (c * (m : Real) * 2 ^ m) := by
        exact div_le_div₀ hnum_bound_nonneg hS.2 hden_pos hG
      _ = ((C / c) * r ^ m) / (m : Real) := by
        have hrpow : r ^ m * 2 ^ m = phi ^ m := by
          rw [← mul_pow]
          congr 1
          dsimp [r]
          ring
        field_simp [hc.ne', hm_pos.ne', htwo_pow_pos.ne', r]
        rw [← hrpow]
        ring
      _ <= (C / c) * r ^ m := by
        have hupper_nonneg : 0 <= (C / c) * r ^ m := by
          exact mul_nonneg (div_nonneg hC hc.le) (pow_nonneg hr_nonneg m)
        exact div_le_self hupper_nonneg hm_ge_one

end Omega.Conclusion
