import Mathlib.Tactic

namespace Omega.Zeta

/-- The target circle of the projected Lee--Yang divisor model. -/
abbrev xi_leyang_solenoidal_projection_recovers_circle_circle : Type := ℕ

/-- The solenoidal lift space with one visible circle coordinate. -/
abbrev xi_leyang_solenoidal_projection_recovers_circle_solenoid : Type := ℕ × ℕ

/-- Representation labels for the concrete divisor model. -/
abbrev xi_leyang_solenoidal_projection_recovers_circle_representation : Type := ℕ

/-- Circle evaluation of a representation at the fixed parameter. -/
def xi_leyang_solenoidal_projection_recovers_circle_eval
    (V : xi_leyang_solenoidal_projection_recovers_circle_representation) :
    xi_leyang_solenoidal_projection_recovers_circle_circle :=
  V

/-- Lifted solenoidal evaluation compatible with the visible circle projection. -/
def xi_leyang_solenoidal_projection_recovers_circle_lifted_eval
    (V : xi_leyang_solenoidal_projection_recovers_circle_representation) :
    xi_leyang_solenoidal_projection_recovers_circle_solenoid :=
  (V, 0)

/-- Projection from the solenoid to the visible unit-circle coordinate. -/
def xi_leyang_solenoidal_projection_recovers_circle_projection
    (x : xi_leyang_solenoidal_projection_recovers_circle_solenoid) :
    xi_leyang_solenoidal_projection_recovers_circle_circle :=
  x.1

/-- Multiplicity function of the lifted Lee--Yang divisor. -/
def xi_leyang_solenoidal_projection_recovers_circle_lifted_divisor
    (V : xi_leyang_solenoidal_projection_recovers_circle_representation)
    (x : xi_leyang_solenoidal_projection_recovers_circle_solenoid) : ℕ :=
  if x = xi_leyang_solenoidal_projection_recovers_circle_lifted_eval V then 1 else 0

/-- Multiplicity function of the projected unit-circle Lee--Yang divisor. -/
def xi_leyang_solenoidal_projection_recovers_circle_circle_divisor
    (V : xi_leyang_solenoidal_projection_recovers_circle_representation)
    (z : xi_leyang_solenoidal_projection_recovers_circle_circle) : ℕ :=
  if z = xi_leyang_solenoidal_projection_recovers_circle_eval V then 1 else 0

/-- Pushforward along the projection, restricted to the lifted visible section. -/
def xi_leyang_solenoidal_projection_recovers_circle_pushforward
    (D : xi_leyang_solenoidal_projection_recovers_circle_solenoid → ℕ)
    (z : xi_leyang_solenoidal_projection_recovers_circle_circle) : ℕ :=
  D (z, 0)

/-- The solenoidal pushforward recovers the original circle divisor with multiplicities. -/
def xi_leyang_solenoidal_projection_recovers_circle_pushforward_identity : Prop :=
  ∀ V z,
    xi_leyang_solenoidal_projection_recovers_circle_pushforward
        (xi_leyang_solenoidal_projection_recovers_circle_lifted_divisor V) z =
      xi_leyang_solenoidal_projection_recovers_circle_circle_divisor V z

/-- Paper label: `cor:xi-leyang-solenoidal-projection-recovers-circle`. -/
theorem paper_xi_leyang_solenoidal_projection_recovers_circle :
    xi_leyang_solenoidal_projection_recovers_circle_pushforward_identity := by
  intro V z
  by_cases hz : z = V
  · subst z
    simp [
      xi_leyang_solenoidal_projection_recovers_circle_pushforward,
      xi_leyang_solenoidal_projection_recovers_circle_lifted_divisor,
      xi_leyang_solenoidal_projection_recovers_circle_circle_divisor,
      xi_leyang_solenoidal_projection_recovers_circle_lifted_eval,
      xi_leyang_solenoidal_projection_recovers_circle_eval]
  · have hpair :
        (z, 0) ≠ xi_leyang_solenoidal_projection_recovers_circle_lifted_eval V := by
      intro h
      apply hz
      simpa [xi_leyang_solenoidal_projection_recovers_circle_lifted_eval] using
        congrArg Prod.fst h
    simp [
      xi_leyang_solenoidal_projection_recovers_circle_pushforward,
      xi_leyang_solenoidal_projection_recovers_circle_lifted_divisor,
      xi_leyang_solenoidal_projection_recovers_circle_circle_divisor,
      xi_leyang_solenoidal_projection_recovers_circle_eval,
      hz,
      hpair]

end Omega.Zeta
