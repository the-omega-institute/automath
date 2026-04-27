import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Boolean encoding of the two signs in the `Z₂ × Z₂` Hadamard table. -/
def xi_time_part9h_z2x2_hadamard_tomography_sign (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The four sector moments `S_{α,β}` in the finite scalar model. -/
noncomputable def xi_time_part9h_z2x2_hadamard_tomography_sector_moment
    (sector : Bool × Bool → ℝ) (α β : Bool) : ℝ :=
  sector (α, β)

/-- The mixed moment obtained from the four sector moments by the Walsh character
`(α,β) ↦ α^s β^t`. -/
noncomputable def xi_time_part9h_z2x2_hadamard_tomography_mixed_moment
    (sector : Bool × Bool → ℝ) (s t : Bool) : ℝ :=
  ∑ α : Bool, ∑ β : Bool,
    (if s then xi_time_part9h_z2x2_hadamard_tomography_sign α else 1) *
      (if t then xi_time_part9h_z2x2_hadamard_tomography_sign β else 1) *
        xi_time_part9h_z2x2_hadamard_tomography_sector_moment sector α β

/-- The Hadamard inverse transform recovering a sector moment from the four mixed moments. -/
noncomputable def xi_time_part9h_z2x2_hadamard_tomography_sector_reconstruction
    (sector : Bool × Bool → ℝ) (α β : Bool) : ℝ :=
  ((1 : ℝ) / 4) * ∑ s : Bool, ∑ t : Bool,
    (if s then xi_time_part9h_z2x2_hadamard_tomography_sign α else 1) *
      (if t then xi_time_part9h_z2x2_hadamard_tomography_sign β else 1) *
        xi_time_part9h_z2x2_hadamard_tomography_mixed_moment sector s t

/-- Concrete `Z₂ × Z₂` Walsh--Hadamard tomography package: the mixed moments are the explicit
signed sums over sectors, and the inverse transform recovers every sector moment. -/
def xi_time_part9h_z2x2_hadamard_tomography_statement : Prop :=
  (∀ (sector : Bool × Bool → ℝ) s t,
      xi_time_part9h_z2x2_hadamard_tomography_mixed_moment sector s t =
        ∑ α : Bool, ∑ β : Bool,
          (if s then xi_time_part9h_z2x2_hadamard_tomography_sign α else 1) *
            (if t then xi_time_part9h_z2x2_hadamard_tomography_sign β else 1) *
              xi_time_part9h_z2x2_hadamard_tomography_sector_moment sector α β) ∧
    ∀ (sector : Bool × Bool → ℝ) α β,
      xi_time_part9h_z2x2_hadamard_tomography_sector_reconstruction sector α β =
        xi_time_part9h_z2x2_hadamard_tomography_sector_moment sector α β

/-- Paper label: `thm:xi-time-part9h-z2x2-hadamard-tomography`. -/
theorem paper_xi_time_part9h_z2x2_hadamard_tomography :
    xi_time_part9h_z2x2_hadamard_tomography_statement := by
  constructor
  · intro sector s t
    rfl
  · intro sector α β
    cases α <;> cases β <;>
      simp [xi_time_part9h_z2x2_hadamard_tomography_sector_reconstruction,
        xi_time_part9h_z2x2_hadamard_tomography_mixed_moment,
        xi_time_part9h_z2x2_hadamard_tomography_sector_moment,
        xi_time_part9h_z2x2_hadamard_tomography_sign] <;>
      ring

end Omega.Zeta
