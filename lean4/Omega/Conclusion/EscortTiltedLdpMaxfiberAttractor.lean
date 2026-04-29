import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete escort tilted-LDP package.  The fields are the cumulant transform, base rate
function, tilted rate, and a closed-set upper-bound certificate for the max-fiber lower tail. -/
structure conclusion_escort_tilted_ldp_maxfiber_attractor_data where
  conclusion_escort_tilted_ldp_maxfiber_attractor_Lambda : ℝ → ℝ
  conclusion_escort_tilted_ldp_maxfiber_attractor_LambdaInfinity : ℝ
  conclusion_escort_tilted_ldp_maxfiber_attractor_rate : ℝ → ℝ
  conclusion_escort_tilted_ldp_maxfiber_attractor_tiltedRate : ℝ → ℝ → ℝ
  conclusion_escort_tilted_ldp_maxfiber_attractor_tailExponent : ℝ → ℝ → ℝ
  conclusion_escort_tilted_ldp_maxfiber_attractor_infClosedRate : ℝ → ℝ → ℝ
  conclusion_escort_tilted_ldp_maxfiber_attractor_tilt_transfer :
    ∀ a y : ℝ, 0 < a →
      conclusion_escort_tilted_ldp_maxfiber_attractor_tiltedRate a y =
        conclusion_escort_tilted_ldp_maxfiber_attractor_rate y - a * y +
          conclusion_escort_tilted_ldp_maxfiber_attractor_Lambda a
  conclusion_escort_tilted_ldp_maxfiber_attractor_frozen_pressure :
    ∀ a : ℝ, 0 < a →
      conclusion_escort_tilted_ldp_maxfiber_attractor_Lambda a =
        a * conclusion_escort_tilted_ldp_maxfiber_attractor_LambdaInfinity
  conclusion_escort_tilted_ldp_maxfiber_attractor_closed_set_upper_bound :
    ∀ a ε : ℝ, 0 < a → 0 < ε →
      conclusion_escort_tilted_ldp_maxfiber_attractor_tailExponent a ε ≤
        -conclusion_escort_tilted_ldp_maxfiber_attractor_infClosedRate a ε
  conclusion_escort_tilted_ldp_maxfiber_attractor_infClosedRate_lower :
    ∀ a ε : ℝ, 0 < a → 0 < ε →
      a * ε ≤ conclusion_escort_tilted_ldp_maxfiber_attractor_infClosedRate a ε

namespace conclusion_escort_tilted_ldp_maxfiber_attractor_data

/-- Exponential tilting transfers the original LDP to the tilted rate function. -/
def conclusion_escort_tilted_ldp_maxfiber_attractor_tilted_rate_function
    (D : conclusion_escort_tilted_ldp_maxfiber_attractor_data) : Prop :=
  ∀ a y : ℝ, 0 < a →
    D.conclusion_escort_tilted_ldp_maxfiber_attractor_tiltedRate a y =
      D.conclusion_escort_tilted_ldp_maxfiber_attractor_rate y - a * y +
        D.conclusion_escort_tilted_ldp_maxfiber_attractor_Lambda a

/-- In the frozen phase, the cumulant transform is the affine ray `Λ(a)=aΛ∞`. -/
def conclusion_escort_tilted_ldp_maxfiber_attractor_frozen_rate_function
    (D : conclusion_escort_tilted_ldp_maxfiber_attractor_data) : Prop :=
  ∀ a y : ℝ, 0 < a →
    D.conclusion_escort_tilted_ldp_maxfiber_attractor_tiltedRate a y =
      D.conclusion_escort_tilted_ldp_maxfiber_attractor_rate y +
        a * (D.conclusion_escort_tilted_ldp_maxfiber_attractor_LambdaInfinity - y)

/-- The tilted law assigns exponentially small mass to the closed lower tail below the
max-fiber level. -/
def conclusion_escort_tilted_ldp_maxfiber_attractor_maxfiber_tail_bound
    (D : conclusion_escort_tilted_ldp_maxfiber_attractor_data) : Prop :=
  ∀ a ε : ℝ, 0 < a → 0 < ε →
    D.conclusion_escort_tilted_ldp_maxfiber_attractor_tailExponent a ε ≤ -(a * ε)

end conclusion_escort_tilted_ldp_maxfiber_attractor_data

open conclusion_escort_tilted_ldp_maxfiber_attractor_data

/-- Paper label: `thm:conclusion-escort-tilted-ldp-maxfiber-attractor`. -/
theorem paper_conclusion_escort_tilted_ldp_maxfiber_attractor
    (D : conclusion_escort_tilted_ldp_maxfiber_attractor_data) :
    D.conclusion_escort_tilted_ldp_maxfiber_attractor_tilted_rate_function ∧
      D.conclusion_escort_tilted_ldp_maxfiber_attractor_frozen_rate_function ∧
      D.conclusion_escort_tilted_ldp_maxfiber_attractor_maxfiber_tail_bound := by
  refine ⟨?_, ?_, ?_⟩
  · intro a y ha
    exact D.conclusion_escort_tilted_ldp_maxfiber_attractor_tilt_transfer a y ha
  · intro a y ha
    rw [D.conclusion_escort_tilted_ldp_maxfiber_attractor_tilt_transfer a y ha,
      D.conclusion_escort_tilted_ldp_maxfiber_attractor_frozen_pressure a ha]
    ring
  · intro a ε ha hε
    have hupper :=
      D.conclusion_escort_tilted_ldp_maxfiber_attractor_closed_set_upper_bound a ε ha hε
    have hlower :=
      D.conclusion_escort_tilted_ldp_maxfiber_attractor_infClosedRate_lower a ε ha hε
    linarith

end Omega.Conclusion
