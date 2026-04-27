import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete phase-lift data for the Ramanujan spectral-bound principle.  Each visible scalar lies
in `[-2, 2]`, so it is the real trace `2 c` of a point `(c, s)` on the unit circle. -/
structure ramanujan_phase_lift_principle_data where
  ramanujan_phase_lift_principle_index : Type
  ramanujan_phase_lift_principle_spectralParameter :
    ramanujan_phase_lift_principle_index → ℝ
  ramanujan_phase_lift_principle_spectralBound :
    ∀ α, -2 ≤ ramanujan_phase_lift_principle_spectralParameter α ∧
      ramanujan_phase_lift_principle_spectralParameter α ≤ 2

namespace ramanujan_phase_lift_principle_data

/-- Real part of the unit-circle lift. -/
noncomputable def phaseReal (D : ramanujan_phase_lift_principle_data)
    (α : D.ramanujan_phase_lift_principle_index) : ℝ :=
  D.ramanujan_phase_lift_principle_spectralParameter α / 2

/-- Nonnegative imaginary part of the unit-circle lift. -/
noncomputable def phaseImag (D : ramanujan_phase_lift_principle_data)
    (α : D.ramanujan_phase_lift_principle_index) : ℝ :=
  Real.sqrt (1 - D.phaseReal α ^ 2)

/-- The explicit scalar phase lift. -/
noncomputable def unitaryPhaseLift (D : ramanujan_phase_lift_principle_data)
    (α : D.ramanujan_phase_lift_principle_index) : ℝ × ℝ :=
  (D.phaseReal α, D.phaseImag α)

/-- Unit-circle predicate for a scalar phase. -/
def isUnitaryPhase (z : ℝ × ℝ) : Prop :=
  z.1 ^ 2 + z.2 ^ 2 = 1

/-- The visible self-adjoint scalar is the trace `z + z^{-1} = 2 Re z`. -/
def realizesVisibleScalar (r : ℝ) (z : ℝ × ℝ) : Prop :=
  r = 2 * z.1

/-- Spectral-bound hypotheses imply existence of unitary scalar phase lifts. -/
def spectralBoundImpliesUnitaryLift (D : ramanujan_phase_lift_principle_data) : Prop :=
  ∀ α, ∃ z : ℝ × ℝ, isUnitaryPhase z ∧
    realizesVisibleScalar (D.ramanujan_phase_lift_principle_spectralParameter α) z

end ramanujan_phase_lift_principle_data

/-- Paper label: `thm:ramanujan-phase-lift-principle`. -/
theorem paper_ramanujan_phase_lift_principle (D : ramanujan_phase_lift_principle_data) :
    D.spectralBoundImpliesUnitaryLift := by
  intro α
  refine ⟨D.unitaryPhaseLift α, ?_, ?_⟩
  · dsimp [ramanujan_phase_lift_principle_data.unitaryPhaseLift,
      ramanujan_phase_lift_principle_data.isUnitaryPhase,
      ramanujan_phase_lift_principle_data.phaseImag]
    let c := D.phaseReal α
    have hbound := D.ramanujan_phase_lift_principle_spectralBound α
    have hc_le : c ≤ 1 := by
      dsimp [c, ramanujan_phase_lift_principle_data.phaseReal]
      nlinarith [hbound.2]
    have hc_ge : -1 ≤ c := by
      dsimp [c, ramanujan_phase_lift_principle_data.phaseReal]
      nlinarith [hbound.1]
    have hone_add : 0 ≤ 1 + c := by linarith
    have hone_sub : 0 ≤ 1 - c := by linarith
    have hnonneg : 0 ≤ 1 - c ^ 2 := by
      have hmul : 0 ≤ (1 - c) * (1 + c) := mul_nonneg hone_sub hone_add
      nlinarith
    change c ^ 2 + Real.sqrt (1 - c ^ 2) ^ 2 = 1
    rw [Real.sq_sqrt hnonneg]
    ring
  · dsimp [ramanujan_phase_lift_principle_data.unitaryPhaseLift,
      ramanujan_phase_lift_principle_data.realizesVisibleScalar,
      ramanujan_phase_lift_principle_data.phaseReal]
    ring

end Omega.Zeta
