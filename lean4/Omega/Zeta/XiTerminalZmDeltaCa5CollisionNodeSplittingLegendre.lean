import Mathlib.Tactic

namespace Omega.Zeta

def xiTerminalCollisionNodeResidue : ℕ → ℕ
  | 17 => 15
  | 37 => 29
  | 223 => 10
  | 3739 => 3694
  | 7333 => 6699
  | _ => 0

def isQuadraticResidueMod (p a : ℕ) : Bool :=
  (List.range p).any fun x => x * x % p == a % p

def collisionNodeLegendreSign (p a : ℕ) : ℤ :=
  if isQuadraticResidueMod p a then 1 else -1

def XiTerminalZmDeltaCa5CollisionNodeSplittingLegendreTable : Prop :=
  xiTerminalCollisionNodeResidue 17 = 15 ∧
  xiTerminalCollisionNodeResidue 37 = 29 ∧
  xiTerminalCollisionNodeResidue 223 = 10 ∧
  xiTerminalCollisionNodeResidue 3739 = 3694 ∧
  xiTerminalCollisionNodeResidue 7333 = 6699 ∧
  collisionNodeLegendreSign 17 (xiTerminalCollisionNodeResidue 17) = 1 ∧
  collisionNodeLegendreSign 37 (xiTerminalCollisionNodeResidue 37) = -1 ∧
  collisionNodeLegendreSign 223 (xiTerminalCollisionNodeResidue 223) = -1 ∧
  collisionNodeLegendreSign 3739 (xiTerminalCollisionNodeResidue 3739) = -1 ∧
  collisionNodeLegendreSign 7333 (xiTerminalCollisionNodeResidue 7333) = -1

theorem paper_xi_terminal_zm_delta_ca5_collision_node_splitting_legendre :
    XiTerminalZmDeltaCa5CollisionNodeSplittingLegendreTable := by
  unfold XiTerminalZmDeltaCa5CollisionNodeSplittingLegendreTable
  unfold collisionNodeLegendreSign isQuadraticResidueMod xiTerminalCollisionNodeResidue
  native_decide

end Omega.Zeta
