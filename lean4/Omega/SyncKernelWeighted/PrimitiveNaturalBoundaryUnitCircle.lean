import Mathlib.Tactic
import Omega.SyncKernelWeighted.MuPochhammerNecklaceExpansion
import Omega.SyncKernelWeighted.PressureUnitCircleBranchAngles
import Omega.SyncKernelWeighted.RealInput40PrimedirichletDenseBranch

namespace Omega.SyncKernelWeighted

noncomputable section

/-- A fixed audited branch-angle package used in the primitive natural-boundary wrapper. -/
def primitive_natural_boundary_unit_circle_branch_data : PressureUnitCircleBranchAnglesData where
  t1 := Real.pi / 3
  t2 := 2 * Real.pi / 3
  t3 := Real.pi
  ht1 := rfl
  ht2 := by ring
  ht3 := rfl

/-- Every open angular interval contains branch points whose real part is arbitrarily small and
whose imaginary part lands inside that interval. This is the concrete local obstruction used to
encode the natural-boundary mechanism. -/
def primitive_natural_boundary_unit_circle_arc_obstructed (a b : ℝ) : Prop :=
  a < b →
    ∀ ε : ℝ, 0 < ε →
      ∃ n : ℕ, ∃ y : ℝ,
        y ∈ realInput40DenseBranchHeights ∧
          a < y ∧
          y < b ∧
          |(realInput40BohrBranchPoint n y).re| < ε

/-- Concrete statement packaging the explicit Möbius/Pochhammer coefficient formula, the certified
unit-circle branch angles, and the interval-by-interval branch obstruction approaching the unit
circle. -/
def primitive_natural_boundary_unit_circle_statement : Prop :=
  (∀ α n : ℕ, 1 ≤ n →
    mu_pochhammer_necklace_expansion_coefficient α n =
      (∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius d : ℚ) * (α : ℚ) ^ (n / d)) / n) ∧
    (0 < primitive_natural_boundary_unit_circle_branch_data.t1 ∧
      primitive_natural_boundary_unit_circle_branch_data.t1 <
        primitive_natural_boundary_unit_circle_branch_data.t2 ∧
      primitive_natural_boundary_unit_circle_branch_data.t2 <
        primitive_natural_boundary_unit_circle_branch_data.t3 ∧
      primitive_natural_boundary_unit_circle_branch_data.t3 ≤ Real.pi ∧
      primitive_natural_boundary_unit_circle_branch_data.isBranchAngle
          primitive_natural_boundary_unit_circle_branch_data.t1 ∧
      primitive_natural_boundary_unit_circle_branch_data.isBranchAngle
          primitive_natural_boundary_unit_circle_branch_data.t2 ∧
      primitive_natural_boundary_unit_circle_branch_data.isBranchAngle
          primitive_natural_boundary_unit_circle_branch_data.t3 ∧
      ∀ t : ℝ,
        0 < t →
          t ≤ Real.pi →
            primitive_natural_boundary_unit_circle_branch_data.isBranchAngle t →
              t = primitive_natural_boundary_unit_circle_branch_data.t1 ∨
                t = primitive_natural_boundary_unit_circle_branch_data.t2 ∨
                  t = primitive_natural_boundary_unit_circle_branch_data.t3) ∧
    (∀ a b : ℝ, primitive_natural_boundary_unit_circle_arc_obstructed a b)

private lemma primitive_natural_boundary_unit_circle_arc_obstructed_of_dense_branch (a b : ℝ) :
    primitive_natural_boundary_unit_circle_arc_obstructed a b := by
  intro hab ε hε
  rcases paper_real_input_40_primedirichlet_dense_branch with ⟨_, _, hNearAxis⟩
  let t : ℝ := (a + b) / 2
  let δ : ℝ := min ε ((b - a) / 2)
  have hδpos : 0 < δ := by
    have hwidth : 0 < (b - a) / 2 := by linarith
    exact lt_min hε hwidth
  rcases hNearAxis t δ hδpos with ⟨n, y, hy, hre, him⟩
  refine ⟨n, y, hy, ?_, ?_, ?_⟩
  · have hyclose : |y - t| < (b - a) / 2 := by
      calc
        |y - t| = |(realInput40BohrBranchPoint n y).im - t| := by simp [realInput40BohrBranchPoint]
        _ < δ := him
        _ ≤ (b - a) / 2 := min_le_right _ _
    have hybounds := abs_lt.mp hyclose
    dsimp [t] at hybounds
    linarith
  · have hyclose : |y - t| < (b - a) / 2 := by
      calc
        |y - t| = |(realInput40BohrBranchPoint n y).im - t| := by simp [realInput40BohrBranchPoint]
        _ < δ := him
        _ ≤ (b - a) / 2 := min_le_right _ _
    have hybounds := abs_lt.mp hyclose
    dsimp [t] at hybounds
    linarith
  · exact lt_of_lt_of_le hre (min_le_left _ _)

/-- Paper label: `thm:primitive-natural-boundary-unit-circle`. -/
theorem paper_primitive_natural_boundary_unit_circle :
    primitive_natural_boundary_unit_circle_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro α n hn
    exact (paper_mu_pochhammer_necklace_expansion α).1 n hn
  · exact paper_pressure_unit_circle_branch_angles primitive_natural_boundary_unit_circle_branch_data
  · intro a b
    exact primitive_natural_boundary_unit_circle_arc_obstructed_of_dense_branch a b

end

end Omega.SyncKernelWeighted
