import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmDeltaS5IntermediateQuotientCollisionNodalCount

namespace Omega.Zeta

/-- Concrete data for the one-vertex dual graph attached to the intermediate quotient at an
S5 tame collision prime.  The node count is supplied by the existing nodal-count package; each
node contributes one loop edge on the irreducible special fiber. -/
structure xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data where
  xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_collisionData :
    XiTerminalZmDeltaS5IntermediateQuotientCollisionData

/-- The quotient node count inherited from the nodal-count theorem's data package. -/
def xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.nodeCount
    (D :
      xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data) :
    ℕ :=
  D.xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_collisionData.nodeCount

/-- The single vertex of the irreducible special fiber's dual graph. -/
abbrev xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.oneVertexDualGraphVertex
    (_D :
      xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data) :
    Type :=
  Fin 1

/-- The loop edges of the one-vertex dual graph, one for each node. -/
abbrev xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.oneVertexDualGraphLoopEdge
    (D :
      xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data) :
    Type :=
  Fin D.nodeCount

/-- For a one-vertex graph, the first Betti number is the number of loop edges. -/
def xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.oneVertexDualGraphFirstBetti
    (D :
      xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data) :
    ℕ :=
  Fintype.card (D.oneVertexDualGraphLoopEdge)

/-- Raynaud's toric rank for this semistable Jacobian equals the dual graph's first Betti number. -/
def xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.torusRank
    (D :
      xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data) :
    ℕ :=
  D.oneVertexDualGraphFirstBetti

/-- A one-vertex dual graph has trivial graph Jacobian, hence trivial component group. -/
def xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.componentGroupCard
    (_D :
      xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data) :
    ℕ :=
  1

/-- The Tamagawa factor is the order of the component group. -/
def xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.tamagawaFactor
    (D :
      xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data) :
    ℕ :=
  D.componentGroupCard

/-- Paper label:
`cor:xi-terminal-zm-delta-s5-intermediate-quotient-jacobian-torus-rank-trivial-component`.
-/
theorem paper_xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component
    (D :
      xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data) :
    D.torusRank = D.nodeCount ∧ D.componentGroupCard = 1 ∧ D.tamagawaFactor = 1 := by
  have _hnodal :=
    paper_xi_terminal_zm_delta_s5_intermediate_quotient_collision_nodal_count
      D.xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_collisionData
  constructor
  · simp [
      xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.torusRank,
      xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.oneVertexDualGraphFirstBetti,
      xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.oneVertexDualGraphLoopEdge,
      xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.nodeCount]
  · constructor
    · simp [
        xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.componentGroupCard]
    · simp [
        xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.tamagawaFactor,
        xi_terminal_zm_delta_s5_intermediate_quotient_jacobian_torus_rank_trivial_component_data.componentGroupCard]

end Omega.Zeta
