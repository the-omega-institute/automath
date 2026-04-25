import Mathlib

namespace Omega.Zeta

/-- A one-pole Abel kernel with pole at `radius`. -/
def damped_poles_abel_kernel (radius r : ℚ) : ℚ :=
  1 / (1 - r / radius)

/-- Damping by `δ` in base `b` rescales the input from `r` to `r / b^δ`. -/
def damped_poles_damped_transform (b : ℚ) (δ : ℕ) (A : ℚ → ℚ) (r : ℚ) : ℚ :=
  A (r / b ^ δ)

/-- The undamped pole radius indexed by the exponent `ρ`. -/
def damped_poles_base_radius (b : ℚ) (ρ : ℕ) : ℚ :=
  b ^ ρ

/-- After damping by `δ`, the pole radius is multiplied by `b^δ`. -/
def damped_poles_rescaled_radius (b : ℚ) (ρ δ : ℕ) : ℚ :=
  b ^ (ρ + δ)

/-- In this concrete model the unit-disk holomorphy criterion is that every damped pole lies
outside `|r| < 1`, equivalently that the rescaled pole radius is `> 1`. -/
def damped_poles_unit_disk_holomorphic_criterion (b : ℚ) (ρ δ : ℕ) : Prop :=
  (1 : ℚ) < damped_poles_rescaled_radius b ρ δ

/-- Paper label: `prop:damped-poles`. Substituting `r / b^δ` into the one-pole Abel kernel moves
the pole from `b^ρ` to `b^(ρ+δ)`, and the unit-disk holomorphy criterion is exactly that this
rescaled pole radius exceed `1`. -/
theorem paper_damped_poles (b : ℚ) (ρ δ : ℕ) (hb : b ≠ 0) :
    (∀ r : ℚ,
      damped_poles_damped_transform b δ
          (damped_poles_abel_kernel (damped_poles_base_radius b ρ)) r =
        damped_poles_abel_kernel (damped_poles_rescaled_radius b ρ δ) r) ∧
      damped_poles_rescaled_radius b ρ δ = damped_poles_base_radius b ρ * b ^ δ ∧
      (damped_poles_unit_disk_holomorphic_criterion b ρ δ ↔
        (1 : ℚ) < damped_poles_base_radius b ρ * b ^ δ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    have hρ : damped_poles_base_radius b ρ ≠ 0 := by
      simp [damped_poles_base_radius, hb]
    have hδ : b ^ δ ≠ 0 := by
      exact pow_ne_zero δ hb
    have hρδ : damped_poles_rescaled_radius b ρ δ ≠ 0 := by
      simp [damped_poles_rescaled_radius, hb]
    unfold damped_poles_damped_transform damped_poles_abel_kernel
      damped_poles_base_radius damped_poles_rescaled_radius
    field_simp [hρ, hδ, hρδ]
    ring
  · simp [damped_poles_rescaled_radius, damped_poles_base_radius, pow_add]
  · simp [damped_poles_unit_disk_holomorphic_criterion, damped_poles_rescaled_radius,
      damped_poles_base_radius, pow_add]

end Omega.Zeta
