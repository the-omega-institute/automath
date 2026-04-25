import Mathlib.Data.Finset.Basic
import Omega.Conclusion.PhaseChannelCrowdingLowerBound

namespace Omega.Conclusion

/-- Number of torus cells in the `M^d` partition with
`M = floor((N + 1) ^ (r / d))`. -/
noncomputable def conclusion_cdim_phase_compression_power_law_cell_count (N r d : ℕ) : ℕ :=
  (Nat.floor ((N + 1 : ℝ) ^ ((r : ℝ) / d))) ^ d

/-- Concrete finite-box data for the `cdim` phase-compression power-law argument. The finite box
is encoded by an injective map from `Fin box.card`, each encoded point is assigned to one of the
`M^d` torus cells, and occupying the same cell forces the stated torus-distance bound. -/
structure conclusion_cdim_phase_compression_power_law_data where
  α : Type
  box : Finset α
  boxIndex : Fin box.card → α
  boxIndex_mem : ∀ i, boxIndex i ∈ box
  boxIndex_injective : Function.Injective boxIndex
  d : ℕ
  hd : 0 < d
  r : ℕ
  N : ℕ
  phi : α → Fin d → ℝ
  torusDist : (Fin d → ℝ) → (Fin d → ℝ) → ℝ
  cellOf : Fin box.card → Fin (conclusion_cdim_phase_compression_power_law_cell_count N r d)
  crowded : conclusion_cdim_phase_compression_power_law_cell_count N r d < box.card
  sameCell_bound :
    ∀ {i j : Fin box.card}, cellOf i = cellOf j →
      torusDist (phi (boxIndex i)) (phi (boxIndex j)) ≤ 2 * (N + 1 : ℝ) ^ (-(r : ℝ) / d)

/-- Reduce the power-law compression setup to the previously formalized finite crowding problem. -/
noncomputable def conclusion_cdim_phase_compression_power_law_phase_channel_data
    (D : conclusion_cdim_phase_compression_power_law_data) : PhaseChannelCrowdingData where
  boxPointCount := D.box.card
  cellCount := conclusion_cdim_phase_compression_power_law_cell_count D.N D.r D.d
  cellOf := D.cellOf
  crowded := D.crowded

/-- Partition the fundamental cube into `M^d` cells with `M = floor((N + 1)^(r/d))`. Since the
finite box contains more encoded points than cells, two distinct box points land in the same cell;
the packaged same-cell estimate then yields the power-law torus-distance bound.
    thm:conclusion-cdim-phase-compression-power-law -/
theorem paper_conclusion_cdim_phase_compression_power_law
    (D : conclusion_cdim_phase_compression_power_law_data) :
    ∃ u v, u ∈ D.box ∧ v ∈ D.box ∧ u ≠ v ∧
      D.torusDist (D.phi u) (D.phi v) ≤ 2 * (D.N + 1 : ℝ) ^ (-(D.r : ℝ) / D.d) := by
  obtain ⟨n, -, -, -⟩ :=
    paper_conclusion_phase_channel_crowding_lb
      (conclusion_cdim_phase_compression_power_law_phase_channel_data D)
  refine ⟨D.boxIndex n.1.1, D.boxIndex n.1.2, D.boxIndex_mem n.1.1, D.boxIndex_mem n.1.2, ?_, ?_⟩
  · intro hEq
    exact n.2.1 (D.boxIndex_injective hEq)
  · simpa [conclusion_cdim_phase_compression_power_law_phase_channel_data] using
      (D.sameCell_bound n.2.2)

end Omega.Conclusion
