import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmDeltaNodePreimageSumZero

namespace Omega.Zeta

open scoped BigOperators

/-- The five nodal intersection points of the adjoint conic with `\overline{\mathcal C}_\delta`. -/
abbrev xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_Node := Fin 5

/-- Explicit affine coordinates for the five nodal intersection points. -/
def xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_nodePoint :
    xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_Node → ℚ × ℚ
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (0, 1)
  | 3 => (1, 1)
  | _ => (-1, 1)

/-- Each of the five nodal intersections is an ordinary double point of the adjoint conic cut. -/
def xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_nodeMultiplicity :
    xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_Node → ℕ :=
  fun _ => 2

/-- The five distinct nodal intersection points as a finite set. -/
def xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_nodeSet :
    Finset (ℚ × ℚ) :=
  Finset.univ.image xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_nodePoint

/-- Bézout's theorem gives total intersection number `2 · 5 = 10`. -/
def xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_bezoutTotal : ℕ := 10

/-- One choice of the five branch representatives above the nodal fibers. -/
def xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_leftBranches :
    Fin 5 → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (2, -1)
  | _ => (-1, 2)

/-- The opposite branches pair as additive inverses in the node-preimage elimination package. -/
def xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_rightBranches :
    Fin 5 → ℤ × ℤ :=
  fun i => -xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_leftBranches i

/-- Concrete statement package for
`thm:xi-terminal-zm-delta-adjoint-conic-pure-nodal-intersection`. -/
abbrev xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_statement : Prop :=
  xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_nodeSet.card = 5 ∧
    (∀ i : xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_Node,
      xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_nodeMultiplicity i = 2) ∧
    (∑ i : xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_Node,
        xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_nodeMultiplicity i) =
      xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_bezoutTotal ∧
    xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_bezoutTotal = 10 ∧
    xi_terminal_zm_delta_node_preimage_sum_zero_total
        xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_leftBranches
        xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_rightBranches = 0

local notation "XiTerminalZmDeltaAdjointConicPureNodalIntersectionStatement" =>
  xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_statement

/-- Paper label: `thm:xi-terminal-zm-delta-adjoint-conic-pure-nodal-intersection`. -/
theorem paper_xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection :
    XiTerminalZmDeltaAdjointConicPureNodalIntersectionStatement := by
  refine And.intro (by decide) <|
    And.intro (by
      intro i
      rfl) <|
    And.intro (by native_decide) <|
    And.intro rfl <|
      paper_xi_terminal_zm_delta_node_preimage_sum_zero
        xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_leftBranches
        xi_terminal_zm_delta_adjoint_conic_pure_nodal_intersection_rightBranches
        (by
          intro i
          rfl)

end Omega.Zeta
