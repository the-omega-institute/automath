import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete semistable quotient data for the tame `S₅` collision package. The quotient has total
size `60`, the free node action turns nodes into `H`-orbits, the dual graph is a one-vertex loop
graph, and the semistable genus decomposition identifies the normalized genus with the torus rank
because the unique component has genus `0`. -/
structure XiTerminalZmDeltaS5TameCollisionEtaleQuotientData where
  stabilizerOrder : ℕ
  quotientSize : ℕ
  nodeOrbitCount : ℕ
  nodeCount : ℕ
  loopCount : ℕ
  torusRank : ℕ
  componentGenus : ℕ
  arithmeticGenus : ℕ
  normalizedGenus : ℕ
  quotientSize_eq : quotientSize = 60
  freeNodeOrbitCount_eq : nodeOrbitCount = quotientSize / stabilizerOrder
  nodeCount_eq_orbitCount : nodeCount = nodeOrbitCount
  loopCount_eq_nodeCount : loopCount = nodeCount
  torusRank_eq_betti : torusRank = loopCount
  semistableGenusDecomposition : arithmeticGenus = componentGenus + torusRank
  componentGenus_eq_zero : componentGenus = 0
  normalizedGenus_eq_arithmeticGenus : normalizedGenus = arithmeticGenus

namespace XiTerminalZmDeltaS5TameCollisionEtaleQuotientData

/-- Orbit counting gives `60 / |H|` quotient nodes. -/
def nodeCountLaw (D : XiTerminalZmDeltaS5TameCollisionEtaleQuotientData) : Prop :=
  D.nodeCount = 60 / D.stabilizerOrder

/-- The one-vertex loop graph has first Betti number equal to its loop count, so the torus rank
matches the node count. -/
def torusRankLaw (D : XiTerminalZmDeltaS5TameCollisionEtaleQuotientData) : Prop :=
  D.torusRank = 60 / D.stabilizerOrder

/-- With a single genus-zero component, the semistable genus decomposition identifies the
normalized genus with the torus rank. -/
def normalizedGenusLaw (D : XiTerminalZmDeltaS5TameCollisionEtaleQuotientData) : Prop :=
  D.normalizedGenus = 60 / D.stabilizerOrder

lemma nodeCountLaw_holds (D : XiTerminalZmDeltaS5TameCollisionEtaleQuotientData) : D.nodeCountLaw := by
  calc
    D.nodeCount = D.nodeOrbitCount := D.nodeCount_eq_orbitCount
    _ = D.quotientSize / D.stabilizerOrder := D.freeNodeOrbitCount_eq
    _ = 60 / D.stabilizerOrder := by rw [D.quotientSize_eq]

lemma torusRankLaw_holds (D : XiTerminalZmDeltaS5TameCollisionEtaleQuotientData) :
    D.torusRankLaw := by
  calc
    D.torusRank = D.loopCount := D.torusRank_eq_betti
    _ = D.nodeCount := D.loopCount_eq_nodeCount
    _ = 60 / D.stabilizerOrder := D.nodeCountLaw_holds

lemma normalizedGenusLaw_holds (D : XiTerminalZmDeltaS5TameCollisionEtaleQuotientData) :
    D.normalizedGenusLaw := by
  calc
    D.normalizedGenus = D.arithmeticGenus := D.normalizedGenus_eq_arithmeticGenus
    _ = D.componentGenus + D.torusRank := D.semistableGenusDecomposition
    _ = 0 + D.torusRank := by rw [D.componentGenus_eq_zero]
    _ = D.torusRank := by simp
    _ = 60 / D.stabilizerOrder := D.torusRankLaw_holds

end XiTerminalZmDeltaS5TameCollisionEtaleQuotientData

open XiTerminalZmDeltaS5TameCollisionEtaleQuotientData

/-- Orbit counting on the free node action gives `60 / |H|` quotient nodes, the one-vertex loop
dual graph has the same first Betti number, and the semistable genus decomposition collapses to
the same value because the unique component has genus `0`.
    prop:xi-terminal-zm-delta-s5-tame-collision-etale-quotient-node-law -/
theorem paper_xi_terminal_zm_delta_s5_tame_collision_etale_quotient_node_law
    (D : XiTerminalZmDeltaS5TameCollisionEtaleQuotientData) :
    D.nodeCountLaw ∧ D.torusRankLaw ∧ D.normalizedGenusLaw := by
  exact ⟨D.nodeCountLaw_holds, D.torusRankLaw_holds, D.normalizedGenusLaw_holds⟩

end Omega.Zeta
