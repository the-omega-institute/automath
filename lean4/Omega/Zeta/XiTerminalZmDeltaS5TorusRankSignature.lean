import Mathlib.Tactic

namespace Omega.Zeta

/-- The six isogeny factors appearing in the tame `S₅` collision package. -/
inductive XiTerminalZmDeltaS5Factor
  | epsilon
  | E
  | B3
  | B5
  | B6
  | B7
  deriving DecidableEq, Repr

/-- Isotypic semistable torus ranks coming from the monodromy-induced conductor vector. -/
def xiTerminalZmDeltaS5IsotypicRank : XiTerminalZmDeltaS5Factor → ℕ
  | .epsilon => 1
  | .E => 4
  | .B3 => 10
  | .B5 => 18
  | .B6 => 15
  | .B7 => 12

/-- Power-isogeny multiplicities from the refinement package
`A_(4,1) ~ E^4`, `A_(3,2) ~ B3^5`, `A_(3,1,1) ~ B5^6`, `A_(2,2,1) ~ B6^5`,
`A_(2,1,1,1) ~ B7^4`. -/
def xiTerminalZmDeltaS5PowerMultiplicity : XiTerminalZmDeltaS5Factor → ℕ
  | .epsilon => 1
  | .E => 4
  | .B3 => 5
  | .B5 => 6
  | .B6 => 5
  | .B7 => 4

/-- Dividing the isotypic torus rank by the corresponding power multiplicity gives the torus rank
of the underlying simple factor. -/
def xiTerminalZmDeltaS5TorusRank (A : XiTerminalZmDeltaS5Factor) : ℕ :=
  xiTerminalZmDeltaS5IsotypicRank A / xiTerminalZmDeltaS5PowerMultiplicity A

/-- Dimensions of the six simple isogeny factors. -/
def xiTerminalZmDeltaS5Dimension : XiTerminalZmDeltaS5Factor → ℕ
  | .epsilon => 2
  | .E => 1
  | .B3 => 3
  | .B5 => 5
  | .B6 => 6
  | .B7 => 7

/-- The abelian-part dimension is `dim - r_p` in the semistable decomposition. -/
def xiTerminalZmDeltaS5AbelianPartDimension (A : XiTerminalZmDeltaS5Factor) : ℕ :=
  xiTerminalZmDeltaS5Dimension A - xiTerminalZmDeltaS5TorusRank A

/-- The rigid torus-rank signature at every tame collision prime in the `S₅` package. -/
def xiTerminalZmDeltaS5TorusRankSignature : Prop :=
  xiTerminalZmDeltaS5TorusRank .E = 1 ∧
    xiTerminalZmDeltaS5TorusRank .B3 = 2 ∧
    xiTerminalZmDeltaS5TorusRank .B5 = 3 ∧
    xiTerminalZmDeltaS5TorusRank .B6 = 3 ∧
    xiTerminalZmDeltaS5TorusRank .B7 = 3 ∧
    xiTerminalZmDeltaS5TorusRank .epsilon = 1 ∧
    xiTerminalZmDeltaS5AbelianPartDimension .E = 0 ∧
    xiTerminalZmDeltaS5AbelianPartDimension .B3 = 1 ∧
    xiTerminalZmDeltaS5AbelianPartDimension .B5 = 2 ∧
    xiTerminalZmDeltaS5AbelianPartDimension .B6 = 3 ∧
    xiTerminalZmDeltaS5AbelianPartDimension .B7 = 4 ∧
    xiTerminalZmDeltaS5AbelianPartDimension .epsilon = 1

/-- Paper label: `thm:xi-terminal-zm-delta-s5-tame-collision-torus-rank-signature`. -/
theorem paper_xi_terminal_zm_delta_s5_tame_collision_torus_rank_signature :
    xiTerminalZmDeltaS5TorusRankSignature := by
  unfold xiTerminalZmDeltaS5TorusRankSignature
  unfold xiTerminalZmDeltaS5AbelianPartDimension
  unfold xiTerminalZmDeltaS5TorusRank
  unfold xiTerminalZmDeltaS5Dimension
  unfold xiTerminalZmDeltaS5IsotypicRank
  unfold xiTerminalZmDeltaS5PowerMultiplicity
  native_decide

end Omega.Zeta
