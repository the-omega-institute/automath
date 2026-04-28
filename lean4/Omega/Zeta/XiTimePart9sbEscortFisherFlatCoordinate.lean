import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The logistic escort coordinate in the square-root odds variable. -/
def xi_time_part9sb_escort_fisher_flat_coordinate_theta (u : ℝ) : ℝ :=
  1 / (1 + u ^ 2)

/-- Fisher density of the square-root odds coordinate. -/
def xi_time_part9sb_escort_fisher_flat_coordinate_fisherDensity (u : ℝ) : ℝ :=
  (2 / (1 + u ^ 2)) ^ 2

/-- The Fisher--Rao flat coordinate. -/
def xi_time_part9sb_escort_fisher_flat_coordinate_psi (u : ℝ) : ℝ :=
  2 * Real.arctan u

/-- The pulled-back Fisher--Rao distance in the flat coordinate. -/
def xi_time_part9sb_escort_fisher_flat_coordinate_distance (p q : ℝ) : ℝ :=
  |xi_time_part9sb_escort_fisher_flat_coordinate_psi q -
    xi_time_part9sb_escort_fisher_flat_coordinate_psi p|

/-- Concrete statement for the flat Fisher coordinate: the arctangent chart differentiates to the
square-root Fisher density, its image lies in the finite open segment `(-π, π)`, and the induced
distance is Euclidean distance in the chart. -/
def xi_time_part9sb_escort_fisher_flat_coordinate_statement : Prop :=
  (∀ u : ℝ,
    HasDerivAt xi_time_part9sb_escort_fisher_flat_coordinate_psi (2 / (1 + u ^ 2)) u) ∧
  (∀ u : ℝ,
    xi_time_part9sb_escort_fisher_flat_coordinate_fisherDensity u =
      (2 / (1 + u ^ 2)) ^ 2) ∧
  (∀ u : ℝ,
    -Real.pi < xi_time_part9sb_escort_fisher_flat_coordinate_psi u ∧
      xi_time_part9sb_escort_fisher_flat_coordinate_psi u < Real.pi) ∧
  (∀ p q : ℝ,
    xi_time_part9sb_escort_fisher_flat_coordinate_distance p q =
      |xi_time_part9sb_escort_fisher_flat_coordinate_psi q -
        xi_time_part9sb_escort_fisher_flat_coordinate_psi p|)

/-- Paper label: `thm:xi-time-part9sb-escort-fisher-flat-coordinate`. -/
theorem paper_xi_time_part9sb_escort_fisher_flat_coordinate :
    xi_time_part9sb_escort_fisher_flat_coordinate_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    simpa [xi_time_part9sb_escort_fisher_flat_coordinate_psi, div_eq_mul_inv] using
      (Real.hasDerivAt_arctan u).const_mul 2
  · intro u
    rfl
  · intro u
    have hlt : Real.arctan u < Real.pi / 2 := Real.arctan_lt_pi_div_two u
    have hgt : -(Real.pi / 2) < Real.arctan u := Real.neg_pi_div_two_lt_arctan u
    constructor <;>
      dsimp [xi_time_part9sb_escort_fisher_flat_coordinate_psi] <;> nlinarith [Real.pi_pos]
  · intro p q
    rfl

end

end Omega.Zeta
