import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The integer-coordinate phase chart used for the Cayley-style unitary parametrization. -/
structure UnitaryTwoIntegerPhase where
  p : Int
  q : Int
deriving DecidableEq, Repr

/-- Multiplication in the integer-coordinate phase chart. -/
instance : Mul UnitaryTwoIntegerPhase where
  mul x y :=
    ⟨x.p * y.q + x.q * y.p, x.q * y.q - x.p * y.p⟩

/-- Inversion in the integer-coordinate phase chart. -/
instance : Inv UnitaryTwoIntegerPhase where
  inv x := ⟨-x.p, x.q⟩

/-- The coordinate map sending an integer pair to its phase-chart representative. -/
def unitaryTwoIntegerMap (p q : Int) : UnitaryTwoIntegerPhase :=
  ⟨p, q⟩

/-- In phase coordinates, multiplication is closed under the bilinear law
`(p,q) * (p',q') = (pq' + qp', qq' - pp')`, and inversion flips the sign of `p`.
    prop:unitary-two-integer-closure -/
theorem paper_unitary_two_integer_closure (p q p' q' : Int) :
    let p'' : Int := p * q' + q * p'
    let q'' : Int := q * q' - p * p'
    unitaryTwoIntegerMap p q * unitaryTwoIntegerMap p' q' = unitaryTwoIntegerMap p'' q'' ∧
      (unitaryTwoIntegerMap p q)⁻¹ = unitaryTwoIntegerMap (-p) q := by
  dsimp [unitaryTwoIntegerMap]
  constructor <;> rfl

end Omega.UnitCirclePhaseArithmetic
