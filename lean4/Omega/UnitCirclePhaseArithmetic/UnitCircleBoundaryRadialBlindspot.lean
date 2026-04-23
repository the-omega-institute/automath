import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppCayleyUpperhalfDisk

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Concrete off-critical boundary-compression package in the fixed Cayley chart. -/
structure unit_circle_boundary_radial_blindspot_data where
  β : ℝ
  γ : ℝ
  rho_max : ℝ
  hβ_upper : β < 1 / 2
  hγ_large : 1 ≤ |γ|
  radius_budget : rho_max ≤ ‖appCayleyUpperHalfMap ((γ : ℂ) + ((1 / 2 : ℝ) - β) * Complex.I)‖

namespace unit_circle_boundary_radial_blindspot_data

/-- The off-critical defect parameter `δ = 1/2 - β`. -/
def delta (D : unit_circle_boundary_radial_blindspot_data) : ℝ :=
  (1 / 2 : ℝ) - D.β

/-- The Cayley image of the off-critical point in the fixed upper-half-plane chart. -/
def w_rho (D : unit_circle_boundary_radial_blindspot_data) : ℂ :=
  appCayleyUpperHalfMap ((D.γ : ℂ) + D.delta * Complex.I)

/-- Exact boundary compression, together with the large-height upper envelope `O(δ / γ²)`. -/
def cayley_boundary_compression (D : unit_circle_boundary_radial_blindspot_data) : Prop :=
  1 - Complex.normSq D.w_rho = 4 * D.delta / (D.γ ^ 2 + (1 + D.delta) ^ 2) ∧
    1 - Complex.normSq D.w_rho ≤ 4 * D.delta / D.γ ^ 2

/-- If the available radius budget stops at `rho_max ≤ |w_ρ|`, the target point has not yet
become visible to that fixed-radius certificate family. -/
def fixed_radius_blindspot (D : unit_circle_boundary_radial_blindspot_data) : Prop :=
  ¬ ‖D.w_rho‖ < D.rho_max

lemma unit_circle_boundary_radial_blindspot_delta_pos
    (D : unit_circle_boundary_radial_blindspot_data) : 0 < D.delta := by
  unfold delta
  linarith [D.hβ_upper]

lemma unit_circle_boundary_radial_blindspot_compression
    (D : unit_circle_boundary_radial_blindspot_data) : D.cayley_boundary_compression := by
  have hdelta : 0 < D.delta := D.unit_circle_boundary_radial_blindspot_delta_pos
  have hgamma_sq_pos : 0 < D.γ ^ 2 := by
    have hgamma_ne : D.γ ≠ 0 := by
      intro hzero
      have : |D.γ| = 0 := by simpa [hzero]
      linarith [D.hγ_large]
    positivity
  have hclosed :
      1 - Complex.normSq D.w_rho = 4 * D.delta / (D.γ ^ 2 + (1 + D.delta) ^ 2) := by
    have hnorm :
        Complex.normSq D.w_rho =
          (D.γ ^ 2 + (1 - D.delta) ^ 2) / (D.γ ^ 2 + (1 + D.delta) ^ 2) := by
      simpa [w_rho] using appCayleyUpperHalf_normSq_formula D.γ D.delta
    rw [hnorm]
    have hden_ne : D.γ ^ 2 + (1 + D.delta) ^ 2 ≠ 0 := by
      exact ne_of_gt (by positivity)
    field_simp [hden_ne]
    ring
  refine ⟨?_, ?_⟩
  · exact hclosed
  · have hnum_nonneg : 0 ≤ 4 * D.delta := by nlinarith [hdelta]
    rw [hclosed]
    refine (div_le_div_of_nonneg_left hnum_nonneg hgamma_sq_pos ?_).trans_eq ?_
    · nlinarith [sq_nonneg (1 + D.delta)]
    · ring

lemma unit_circle_boundary_radial_blindspot_budget
    (D : unit_circle_boundary_radial_blindspot_data) : D.fixed_radius_blindspot := by
  unfold fixed_radius_blindspot
  exact not_lt.mpr (by simpa [w_rho, delta] using D.radius_budget)

end unit_circle_boundary_radial_blindspot_data

open unit_circle_boundary_radial_blindspot_data

/-- Paper label: `prop:unit-circle-boundary-radial-blindspot`. The Cayley image of an
off-critical point is quadratically compressed into the boundary layer, and any fixed-radius
certificate capped below that threshold stays blind until the radius budget itself increases. -/
theorem paper_unit_circle_boundary_radial_blindspot (D : unit_circle_boundary_radial_blindspot_data) :
    D.cayley_boundary_compression ∧ D.fixed_radius_blindspot := by
  exact ⟨D.unit_circle_boundary_radial_blindspot_compression,
    D.unit_circle_boundary_radial_blindspot_budget⟩

end

end Omega.UnitCirclePhaseArithmetic
