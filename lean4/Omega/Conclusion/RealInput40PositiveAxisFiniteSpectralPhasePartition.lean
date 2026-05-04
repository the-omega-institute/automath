import Mathlib

namespace Omega.Conclusion

/-- Concrete data for the positive real axis cut by seven ordered spectral-collision points. The
phase count is the finite interval count induced by those cuts, and local constancy is supplied
away from the collision locus. -/
structure conclusion_realinput40_positive_axis_finite_spectral_phase_partition_data where
  positiveAxisCut : Fin 7 → ℝ
  positiveAxisCut_pos : ∀ i, 0 < positiveAxisCut i
  positiveAxisCut_strictMono : StrictMono positiveAxisCut
  phaseIntervalCount : ℕ
  phaseIntervalCount_eq_cut_count : phaseIntervalCount = Fintype.card (Fin 7) + 1
  spectralBranch : ℕ → ℝ → ℝ
  realSpectralBranchesLocallyConstant_witness :
    ∀ x, 0 < x → (∀ i, x ≠ positiveAxisCut i) →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ y, 0 < y → (∀ i, y ≠ positiveAxisCut i) → |y - x| < ε →
          ∀ branch, spectralBranch branch y = spectralBranch branch x

namespace conclusion_realinput40_positive_axis_finite_spectral_phase_partition_data

/-- The real spectral branches are locally constant on every open phase of the seven-cut
positive-axis partition. -/
def realSpectralBranchesLocallyConstant
    (D : conclusion_realinput40_positive_axis_finite_spectral_phase_partition_data) : Prop :=
  ∀ x, 0 < x → (∀ i, x ≠ D.positiveAxisCut i) →
    ∃ ε : ℝ, 0 < ε ∧
      ∀ y, 0 < y → (∀ i, y ≠ D.positiveAxisCut i) → |y - x| < ε →
        ∀ branch, D.spectralBranch branch y = D.spectralBranch branch x

end conclusion_realinput40_positive_axis_finite_spectral_phase_partition_data

/-- Paper label: `thm:conclusion-realinput40-positive-axis-finite-spectral-phase-partition`. -/
theorem paper_conclusion_realinput40_positive_axis_finite_spectral_phase_partition
    (D : conclusion_realinput40_positive_axis_finite_spectral_phase_partition_data) :
    D.phaseIntervalCount = 8 ∧ D.realSpectralBranchesLocallyConstant := by
  refine ⟨?_, D.realSpectralBranchesLocallyConstant_witness⟩
  rw [D.phaseIntervalCount_eq_cut_count]
  norm_num [Fintype.card_fin]

end Omega.Conclusion
