import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.DerivedWindow6GaugeVolumeDefectIdentity

namespace Omega.Conclusion

/-- The exact gauge-gap defect `Δ₆ = κ₆ - g₆` extracted from the existing window-`6`
gauge-volume/log-density identity. -/
noncomputable def conclusion_window6_gauge_gap_unique_ternary_scar_gap : ℝ :=
  Omega.Zeta.window6GaugeVolumeDensity - Omega.Zeta.window6GaugeLogDensity

/-- Paper-facing window-`6` ternary-scar package. -/
def conclusion_window6_gauge_gap_unique_ternary_scar_statement : Prop :=
  64 * conclusion_window6_gauge_gap_unique_ternary_scar_gap = 49 * Real.log 2 - Real.log 3 ∧
    Real.exp (64 * conclusion_window6_gauge_gap_unique_ternary_scar_gap) = (2 : ℝ) ^ 49 / 3

/-- Paper label: `thm:conclusion-window6-gauge-gap-unique-ternary-scar`. The existing exact
window-`6` gauge defect identity already gives `Δ₆ = (49 log 2 - log 3) / 64`; multiplying by
`64` and exponentiating isolates the unique ternary scar. -/
theorem paper_conclusion_window6_gauge_gap_unique_ternary_scar :
    conclusion_window6_gauge_gap_unique_ternary_scar_statement := by
  rcases Omega.Zeta.paper_derived_window6_gauge_volume_defect_identity with
    ⟨horder, _, _, hgap, hexp_ratio⟩
  refine ⟨?_, ?_⟩
  · calc
      64 * conclusion_window6_gauge_gap_unique_ternary_scar_gap =
          64 * (Omega.Zeta.window6GaugeVolumeDensity - Omega.Zeta.window6GaugeLogDensity) := by
            rfl
      _ = 64 * ((49 * Real.log 2 - Real.log 3) / 64) := by rw [hgap]
      _ = 49 * Real.log 2 - Real.log 3 := by ring
  · have hrewrite :
        64 * conclusion_window6_gauge_gap_unique_ternary_scar_gap =
          64 * Omega.Zeta.window6GaugeVolumeDensity -
            Real.log (Omega.Zeta.window6GaugeGroupOrder : ℝ) := by
      simp [conclusion_window6_gauge_gap_unique_ternary_scar_gap,
        Omega.Zeta.window6GaugeLogDensity]
      ring
    have horder_pos : 0 < (Omega.Zeta.window6GaugeGroupOrder : ℝ) := by
      rw [horder]
      positivity
    calc
      Real.exp (64 * conclusion_window6_gauge_gap_unique_ternary_scar_gap) =
          Real.exp
              (64 * Omega.Zeta.window6GaugeVolumeDensity -
                Real.log (Omega.Zeta.window6GaugeGroupOrder : ℝ)) := by
            rw [hrewrite]
      _ =
          Real.exp (64 * Omega.Zeta.window6GaugeVolumeDensity) /
            Real.exp (Real.log (Omega.Zeta.window6GaugeGroupOrder : ℝ)) := by
            rw [Real.exp_sub]
      _ =
          Real.exp (64 * Omega.Zeta.window6GaugeVolumeDensity) /
            (Omega.Zeta.window6GaugeGroupOrder : ℝ) := by
            rw [Real.exp_log horder_pos]
      _ = (2 : ℝ) ^ 49 / 3 := hexp_ratio

end Omega.Conclusion
