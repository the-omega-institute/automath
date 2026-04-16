import Mathlib.Tactic

namespace Omega.SPG

/-- Chapter-local ledger for the complementarity inequality between gauge volume density and area
density. The entropy identity rewrites the gauge term as a dyadic entropy deficit, and the second
bound packages the factorial/area estimate on that deficit. -/
structure GaugeVolumeAreaComplementarityData where
  dimension : ℕ
  gaugeDensity : ℝ
  areaDensity : ℝ
  fiberEntropyGap : ℝ
  dimension_pos : 0 < dimension
  entropyIdentity :
    gaugeDensity = (dimension : ℝ) * Real.log 2 - fiberEntropyGap
  entropyGapBound :
    fiberEntropyGap ≤ (dimension : ℝ) * (Real.log 2 * areaDensity) + 1

/-- Gauge-volume density and area density satisfy the stated complementarity lower bound.
    thm:spg-gauge-volume-area-complementarity -/
theorem paper_spg_gauge_volume_area_complementarity (h : GaugeVolumeAreaComplementarityData) :
    h.gaugeDensity / (h.dimension : ℝ) + Real.log 2 * h.areaDensity ≥
      Real.log 2 - 1 / (h.dimension : ℝ) := by
  have hdim_pos : 0 < (h.dimension : ℝ) := by
    exact_mod_cast h.dimension_pos
  have hdim_ne : (h.dimension : ℝ) ≠ 0 := by linarith
  have hmain :
      h.gaugeDensity / (h.dimension : ℝ) + Real.log 2 * h.areaDensity =
        Real.log 2 - h.fiberEntropyGap / (h.dimension : ℝ) + Real.log 2 * h.areaDensity := by
    rw [h.entropyIdentity]
    field_simp [hdim_ne]
  rw [hmain]
  have hscaled :
      h.fiberEntropyGap / (h.dimension : ℝ) ≤ Real.log 2 * h.areaDensity + 1 / (h.dimension : ℝ) :=
    by
      rw [_root_.div_le_iff₀ hdim_pos]
      simpa [add_mul, hdim_ne, mul_add, mul_assoc, mul_left_comm, mul_comm] using
        h.entropyGapBound
  linarith

end Omega.SPG
