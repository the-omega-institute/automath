import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the separation between measure sparsity and extremal rigidity. The spherical
phase mass and the extremal depths are real-valued asymptotic profiles indexed by resolution. -/
structure conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_data where
  conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sphericalMass :
    ℕ → ℝ
  conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sphericalDepth :
    ℕ → ℝ
  conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_ambientDepth :
    ℕ → ℝ
  conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sparseRate : ℝ
  conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sparseRate_pos :
    0 <
      conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sparseRate
  conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sparseStage : ℕ
  conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sparse_bound :
    ∀ m,
      conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sparseStage ≤ m →
      conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sphericalMass m ≤
        Real.exp
          (-(conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sparseRate *
            (m : ℝ)))
  conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_depthConstant : ℝ
  conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_depthConstant_pos :
    0 <
      conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_depthConstant
  conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_depthStage : ℕ
  conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_extremal_lower :
    ∀ m,
      conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_depthStage ≤ m →
      conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_depthConstant *
          conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_ambientDepth m ≤
        conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sphericalDepth m

namespace conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_data

/-- The spherical phase has exponentially small counting mass. -/
def exponentially_sparse
    (D : conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_data) : Prop :=
  ∃ c > 0, ∃ M, ∀ m, M ≤ m →
    D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sphericalMass m ≤
      Real.exp (-(c * (m : ℝ)))

/-- The extremal spherical fiber keeps a positive fraction of the ambient extremal depth. -/
def extremal_rigid
    (D : conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_data) : Prop :=
  ∃ c > 0, ∃ M, ∀ m, M ≤ m →
    c * D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_ambientDepth m ≤
      D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sphericalDepth m

/-- Positive liminf-ratio certificate, expressed as the same eventual lower comparison. -/
def positive_ratio
    (D : conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_data) : Prop :=
  ∃ c > 0, ∃ M, ∀ m, M ≤ m →
    c * D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_ambientDepth m ≤
      D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sphericalDepth m

end conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_data

open conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_data

/-- Paper label:
`thm:conclusion-spherical-phase-measure-sparsity-extremal-rigidity-separation`. -/
theorem paper_conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation
    (D : conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_data) :
    D.exponentially_sparse ∧ D.extremal_rigid ∧ D.positive_ratio := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      ⟨D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sparseRate,
        D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sparseRate_pos,
        D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sparseStage,
        D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_sparse_bound⟩
  · exact
      ⟨D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_depthConstant,
        D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_depthConstant_pos,
        D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_depthStage,
        D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_extremal_lower⟩
  · exact
      ⟨D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_depthConstant,
        D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_depthConstant_pos,
        D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_depthStage,
        D.conclusion_spherical_phase_measure_sparsity_extremal_rigidity_separation_extremal_lower⟩

end Omega.Conclusion
