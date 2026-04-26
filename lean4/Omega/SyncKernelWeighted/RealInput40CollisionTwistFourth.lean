import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40CollisionCumulants
import Omega.SyncKernelWeighted.RealInput40CollisionCumulantsHigher

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The quartic Taylor jet of the small-angle twist expansion for
`log (ρ(t) / λ)`. -/
def real_input_40_collision_twist_fourth_log_jet (t : ℝ) : ℝ :=
  -((6 * Real.sqrt 5 - 5) / 250) * t ^ 2 + ((7 + 24 * Real.sqrt 5) / 75000) * t ^ 4

/-- Paper-facing coefficient package for the quartic twist jet. -/
abbrev real_input_40_collision_twist_fourth_statement : Prop :=
  Omega.Zeta.arityCollisionPerronRoot = goldenRatio ^ 2 ∧
    ∀ t : ℝ,
      -(real_input_40_collision_cumulants_second_derivative / 2) * t ^ 2 +
          (real_input_40_collision_cumulants_higher_fourth_derivative / 24) * t ^ 4 =
        real_input_40_collision_twist_fourth_log_jet t

/-- Paper label: `cor:real-input-40-collision-twist-fourth`. -/
theorem paper_real_input_40_collision_twist_fourth :
    real_input_40_collision_twist_fourth_statement := by
  rcases paper_real_input_40_collision_cumulants with ⟨hlam, _, h2⟩
  rcases paper_real_input_40_collision_cumulants_higher with ⟨_, h4⟩
  refine ⟨hlam, ?_⟩
  intro t
  rw [h2, h4, real_input_40_collision_twist_fourth_log_jet]
  ring

end

end Omega.SyncKernelWeighted
