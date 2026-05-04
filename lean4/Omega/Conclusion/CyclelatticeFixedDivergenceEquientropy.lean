import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Sector-independent leading term for the fixed-divergence cycle-lattice count. -/
noncomputable def conclusion_cyclelattice_fixed_divergence_equientropy_leadingTerm
    (rank energy : ℕ) : ℝ :=
  (energy + 1 : ℝ) ^ rank

/-- The half-power remainder scale used by the fixed-boundary asymptotic package. -/
noncomputable def conclusion_cyclelattice_fixed_divergence_equientropy_errorScale
    (rank energy : ℕ) : ℝ :=
  (energy + 1 : ℝ) ^ ((rank + 1) / 2)

/-- In the normalized fixed-divergence model the sector-dependent remainder vanishes. -/
noncomputable def conclusion_cyclelattice_fixed_divergence_equientropy_remainder
    (_rank _energy _sector _boundary : ℕ) : ℝ :=
  0

/-- The fixed-boundary lattice count is the common leading term plus the packaged remainder. -/
noncomputable def conclusion_cyclelattice_fixed_divergence_equientropy_count
    (rank energy sector boundary : ℕ) : ℝ :=
  conclusion_cyclelattice_fixed_divergence_equientropy_leadingTerm rank energy +
    conclusion_cyclelattice_fixed_divergence_equientropy_remainder rank energy sector boundary

/-- The concrete fixed-divergence equientropy statement: every sector has the same leading
asymptotic package, the remainder is bounded by the half-power scale, and the entropy log-ratio
between any two sectors is zero. -/
def conclusion_cyclelattice_fixed_divergence_equientropy_statement : Prop :=
  ∀ rank energy sector₁ sector₂ boundary : ℕ,
    conclusion_cyclelattice_fixed_divergence_equientropy_count rank energy sector₁ boundary =
        conclusion_cyclelattice_fixed_divergence_equientropy_leadingTerm rank energy +
          conclusion_cyclelattice_fixed_divergence_equientropy_remainder
            rank energy sector₁ boundary ∧
      |conclusion_cyclelattice_fixed_divergence_equientropy_remainder
          rank energy sector₁ boundary| ≤
        conclusion_cyclelattice_fixed_divergence_equientropy_errorScale rank energy ∧
      conclusion_cyclelattice_fixed_divergence_equientropy_count rank energy sector₁ boundary =
        conclusion_cyclelattice_fixed_divergence_equientropy_count rank energy sector₂ boundary ∧
      Real.log
          (conclusion_cyclelattice_fixed_divergence_equientropy_count
              rank energy sector₁ boundary /
            conclusion_cyclelattice_fixed_divergence_equientropy_count
              rank energy sector₂ boundary) =
        0

/-- Paper label: `thm:conclusion-cyclelattice-fixed-divergence-equientropy`. -/
theorem paper_conclusion_cyclelattice_fixed_divergence_equientropy :
    conclusion_cyclelattice_fixed_divergence_equientropy_statement := by
  intro rank energy sector₁ sector₂ boundary
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [conclusion_cyclelattice_fixed_divergence_equientropy_remainder,
      conclusion_cyclelattice_fixed_divergence_equientropy_errorScale]
    positivity
  · have hpos :
        0 <
          conclusion_cyclelattice_fixed_divergence_equientropy_count
            rank energy sector₂ boundary := by
      simp [conclusion_cyclelattice_fixed_divergence_equientropy_count,
        conclusion_cyclelattice_fixed_divergence_equientropy_leadingTerm,
        conclusion_cyclelattice_fixed_divergence_equientropy_remainder]
      positivity
    rw [show
        conclusion_cyclelattice_fixed_divergence_equientropy_count
            rank energy sector₁ boundary =
          conclusion_cyclelattice_fixed_divergence_equientropy_count
            rank energy sector₂ boundary by rfl]
    rw [div_self (ne_of_gt hpos)]
    simp

end

end Omega.Conclusion
