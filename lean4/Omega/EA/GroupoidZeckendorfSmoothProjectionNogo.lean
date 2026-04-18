import Mathlib

namespace Omega.EA

/-- Concrete `C^1` chain-rule obstruction for a smooth hidden trajectory in a finite-dimensional
state space (`ℝ × ℝ`) and a smooth scalar readout. -/
def groupoidZeckendorfSmoothProjectionNogoStatement : Prop :=
  ∀ (γ : ℝ → ℝ × ℝ) (O : ℝ × ℝ → ℝ),
    ContDiff ℝ 1 γ → ContDiff ℝ 1 O → ContDiff ℝ 1 (fun t => O (γ t))

/-- A `C^1` hidden trajectory composed with a `C^1` readout is again `C^1`; hence a finite
dimensional smooth hidden state cannot by itself produce an everywhere nondifferentiable visible
signal.
    prop:groupoid-zeckendorf-smooth-projection-nogo -/
theorem paper_groupoid_zeckendorf_smooth_projection_nogo_spec :
    groupoidZeckendorfSmoothProjectionNogoStatement := by
  intro γ O hγ hO
  simpa using hO.comp hγ

/-- Placeholder-signature wrapper requested for the round target.
Lean does not allow a theorem whose type is itself `Prop`, so the round placeholder is realized as
a definition and the verified statement is provided by
`paper_groupoid_zeckendorf_smooth_projection_nogo_verified`. -/
def paper_groupoid_zeckendorf_smooth_projection_nogo : Prop :=
  groupoidZeckendorfSmoothProjectionNogoStatement

theorem paper_groupoid_zeckendorf_smooth_projection_nogo_verified :
    paper_groupoid_zeckendorf_smooth_projection_nogo := by
  exact paper_groupoid_zeckendorf_smooth_projection_nogo_spec

end Omega.EA
