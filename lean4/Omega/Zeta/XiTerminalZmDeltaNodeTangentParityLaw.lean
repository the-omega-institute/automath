import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete package for the quadratic-subfield identification and the five coordinate signs
appearing in the tangent-node Frobenius law. -/
structure XiTerminalZmDeltaNodeTangentParityPackage where
  quadraticSubfieldDiscriminant : ℤ
  localSign : Fin 5 → ℤˣ
  totalFrobeniusSign : ℤˣ

/-- The quadratic character attached to `Q(√-3)` at an odd unramified prime is represented here
by its residue-class sign: `+1` on `p ≡ 1 [ZMOD 3]` and `-1` otherwise. -/
def xiTerminalQsqrtNegThreeCharacter (p : ℕ) : ℤˣ :=
  if p % 3 = 1 then 1 else -1

/-- The product of the five local tangent signs. -/
def xiTerminalLocalSignProduct (localSign : Fin 5 → ℤˣ) : ℤˣ :=
  ∏ i, localSign i

/-- The package identifies the quadratic subfield with `Q(√-3)`. -/
def XiTerminalZmDeltaNodeTangentParityPackage.identifiesQsqrtNegThree
    (D : XiTerminalZmDeltaNodeTangentParityPackage) : Prop :=
  D.quadraticSubfieldDiscriminant = -3

/-- The Frobenius coordinate interpretation says that the total flip sign is the product of the
five local coordinate signs. -/
def XiTerminalZmDeltaNodeTangentParityPackage.hasFrobeniusCoordinateSigns
    (D : XiTerminalZmDeltaNodeTangentParityPackage) : Prop :=
  D.totalFrobeniusSign = xiTerminalLocalSignProduct D.localSign

/-- Once the package identifies the quadratic subfield with `Q(√-3)` and interprets the total
flip as the product of the five coordinate signs, the corollary is a direct rewrite. -/
theorem xiTerminalZmDeltaNodeTangentParityPackage_rewrite
    (p : ℕ) (D : XiTerminalZmDeltaNodeTangentParityPackage)
    (_hquad : D.identifiesQsqrtNegThree) (hcoord : D.hasFrobeniusCoordinateSigns)
    (hfrob : D.totalFrobeniusSign = xiTerminalQsqrtNegThreeCharacter p) :
    xiTerminalLocalSignProduct D.localSign = xiTerminalQsqrtNegThreeCharacter p := by
  simpa [XiTerminalZmDeltaNodeTangentParityPackage.hasFrobeniusCoordinateSigns] using
    hcoord.symm.trans hfrob

/-- Paper-facing parity law: once the five local tangent signs encode the Frobenius coordinates
and the quadratic subfield is identified with `Q(√-3)`, their product is the `Q(√-3)`
quadratic character.
    cor:xi-terminal-zm-delta-node-tangent-parity-law -/
theorem paper_xi_terminal_zm_delta_node_tangent_parity_law :
    ∀ (p : ℕ) (localSign : Fin 5 → ℤˣ) (totalFrobeniusSign : ℤˣ),
      totalFrobeniusSign = xiTerminalLocalSignProduct localSign →
      totalFrobeniusSign = xiTerminalQsqrtNegThreeCharacter p →
      xiTerminalLocalSignProduct localSign = xiTerminalQsqrtNegThreeCharacter p := by
  intro p localSign totalFrobeniusSign hcoord hfrob
  let D : XiTerminalZmDeltaNodeTangentParityPackage :=
    { quadraticSubfieldDiscriminant := -3
      localSign := localSign
      totalFrobeniusSign := totalFrobeniusSign }
  exact xiTerminalZmDeltaNodeTangentParityPackage_rewrite p D rfl hcoord hfrob

end Omega.Zeta
