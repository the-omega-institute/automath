import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.CircleDimension.ComovingDefectDeltaBound

namespace Omega.Zeta.ComovingEnergyDeltaBound

open Omega.CircleDimension.ComovingDefectDeltaBound

set_option maxHeartbeats 400000 in
/-- Paper wrapper: specialize the packaged comoving defect bound to the energy choice
`ε = (1 / 2) log E`, rewrite `exp (-ε)` as `1 / sqrt E`, and enlarge the right-hand side by the
outer `max` to cover the formally negative range. -/
theorem paper_xi_comoving_energy_implies_delta_bound
    {ρ E δ : ℝ} (hρ : 0 < ρ) (hρlt : ρ < 1) (hE : 1 ≤ E) (hδ : 0 ≤ δ)
    (hbound : ρ / Real.sqrt E ≤ (1 - δ) / (1 + δ)) :
    δ ≤ max 0 ((1 - ρ / Real.sqrt E) / (1 + ρ / Real.sqrt E)) := by
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  let ε : ℝ := Real.log E / 2
  have hε : 0 ≤ ε := by
    dsimp [ε]
    have hlog : 0 ≤ Real.log E := Real.log_nonneg hE
    linarith
  have hsqrt_pos : 0 < Real.sqrt E := Real.sqrt_pos.2 hE0
  have hExpHalf : Real.exp ε = Real.sqrt E := by
    dsimp [ε]
    rw [← Real.log_sqrt (show 0 ≤ E by linarith), Real.exp_log hsqrt_pos]
  have hexp : Real.exp (-ε) = 1 / Real.sqrt E := by
    rw [Real.exp_neg, hExpHalf]
    rw [one_div]
  have hbound' : ρ * Real.exp (-ε) ≤ (1 - δ) / (1 + δ) := by
    calc
      ρ * Real.exp (-ε) = ρ / Real.sqrt E := by rw [hexp]; ring
      _ ≤ (1 - δ) / (1 + δ) := hbound
  have hmain :=
    paper_cdim_comoving_defect_implies_delta_bound_package hρ hρlt hε hδ hbound'
  have hmain' : δ ≤ (1 - ρ / Real.sqrt E) / (1 + ρ / Real.sqrt E) := by
    calc
      δ ≤ (1 - ρ * Real.exp (-ε)) / (1 + ρ * Real.exp (-ε)) := hmain
      _ = (1 - ρ / Real.sqrt E) / (1 + ρ / Real.sqrt E) := by
        simp [hexp, div_eq_mul_inv]
  exact le_trans hmain' (le_max_right 0 _)

end Omega.Zeta.ComovingEnergyDeltaBound
