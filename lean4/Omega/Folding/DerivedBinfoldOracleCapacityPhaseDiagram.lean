import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
import Omega.Folding.FoldBinOracleLinearThresholdExponent

open Filter

namespace Omega.Folding

theorem paper_derived_binfold_oracle_capacity_phase_diagram (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto
      (fun m : ℕ => Real.log (Omega.Folding.foldBinOracleSuccess m (a ^ m)) / m)
      Filter.atTop
      (nhds
        (if a < Omega.Folding.foldBinOracleCriticalBase then
          Real.log a - Real.log Omega.Folding.foldBinOracleCriticalBase
        else 0)) := by
  by_cases hlt : a < Omega.Folding.foldBinOracleCriticalBase
  · have hevent :
      (fun m : ℕ => Real.log (Omega.Folding.foldBinOracleSuccess m (a ^ m)) / m) =ᶠ[Filter.atTop]
        (fun _ : ℕ => Real.log a - Real.log Omega.Folding.foldBinOracleCriticalBase) :=
          Filter.eventually_atTop.2 ⟨1, fun m hm =>
            Omega.Folding.foldBinOracleSuccess_below_threshold_log ha hlt hm⟩
    refine Filter.Tendsto.congr' hevent.symm ?_
    simpa [hlt] using
      (tendsto_const_nhds :
        Filter.Tendsto
          (fun _ : ℕ => Real.log a - Real.log Omega.Folding.foldBinOracleCriticalBase)
          Filter.atTop
          (nhds
            (if a < Omega.Folding.foldBinOracleCriticalBase then
              Real.log a - Real.log Omega.Folding.foldBinOracleCriticalBase
            else
              0)))
  · have hge : Omega.Folding.foldBinOracleCriticalBase ≤ a := le_of_not_gt hlt
    by_cases hEq : a = Omega.Folding.foldBinOracleCriticalBase
    · have hevent :
          (fun m : ℕ => Real.log (Omega.Folding.foldBinOracleSuccess m (a ^ m)) / m) =ᶠ[Filter.atTop]
            (fun _ : ℕ => (0 : ℝ)) :=
          Filter.eventually_atTop.2 ⟨0, fun m _ => by
            dsimp
            rw [hEq, Omega.Folding.foldBinOracleSuccess_reduction]
            have hpow_pos : 0 < Omega.Folding.foldBinOracleCriticalBase ^ m := by
              exact pow_pos Omega.Folding.foldBinOracleCriticalBase_pos _
            rw [min_eq_left le_rfl]
            field_simp [ne_of_gt hpow_pos]
            simp⟩
      refine Filter.Tendsto.congr' hevent.symm ?_
      simpa [hlt] using
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop
            (nhds
              (if a < Omega.Folding.foldBinOracleCriticalBase then
                Real.log a - Real.log Omega.Folding.foldBinOracleCriticalBase
              else
                0)))
    · have hne : Omega.Folding.foldBinOracleCriticalBase ≠ a := by
        simpa [eq_comm] using hEq
      have hgt : Omega.Folding.foldBinOracleCriticalBase < a := lt_of_le_of_ne hge hne
      have hevent :
          (fun m : ℕ => Real.log (Omega.Folding.foldBinOracleSuccess m (a ^ m)) / m) =ᶠ[Filter.atTop]
            (fun _ : ℕ => (0 : ℝ)) :=
          Filter.eventually_atTop.2 ⟨1, fun m hm => by
            dsimp
            rw [Omega.Folding.foldBinOracleSuccess_above_threshold hgt hm]
            simp⟩
      refine Filter.Tendsto.congr' hevent.symm ?_
      simpa [hlt] using
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop
            (nhds
              (if a < Omega.Folding.foldBinOracleCriticalBase then
                Real.log a - Real.log Omega.Folding.foldBinOracleCriticalBase
              else
                0)))

end Omega.Folding
