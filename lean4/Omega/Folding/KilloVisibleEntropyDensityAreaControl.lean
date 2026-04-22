import Mathlib.Tactic
import Omega.SPG.GaugeVolumeAreaComplementarity

namespace Omega.Folding

/-- Paper label: `thm:killo-visible-entropy-density-area-control`.
The visible-entropy deficit is exactly the complementarity gap from the SPG area ledger, so the
existing gauge-volume/area estimate gives the claimed upper bound after division by the dimension.
-/
theorem paper_killo_visible_entropy_density_area_control
    (h : Omega.SPG.GaugeVolumeAreaComplementarityData) :
    (((h.dimension : ℝ) * Real.log 2) - h.gaugeDensity) / (h.dimension : ℝ) ≤
      Real.log 2 * h.areaDensity + 1 / (h.dimension : ℝ) := by
  have hdim_pos : 0 < (h.dimension : ℝ) := by
    exact_mod_cast h.dimension_pos
  have hdim_ne : (h.dimension : ℝ) ≠ 0 := by
    linarith
  have hgap :
      ((h.dimension : ℝ) * Real.log 2 - h.gaugeDensity) = h.fiberEntropyGap := by
    linarith [h.entropyIdentity]
  rw [hgap]
  rw [_root_.div_le_iff₀ hdim_pos]
  simpa [add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm, hdim_ne] using
    h.entropyGapBound

end Omega.Folding
