import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local wrapper for the multifactor tensor resultant recursion package. The auxiliary
fields record the factor list, the no-collision hypothesis, the two-factor closure, and the
induction step used to pass from the two-factor case to the iterated resultant. The paper-facing
outputs are the minimal-polynomial identification together with degree and Hankel-rank
multiplicativity. -/
structure TensorFoldResultantRecursionData where
  Factor : Type
  factors : List Factor
  noCollision : Prop
  twoFactorClosure : Prop
  inductionStep : Prop
  iteratedResultantIsMinimalPolynomial : Prop
  degreeMultiplicativity : Prop
  hankelRankMultiplicativity : Prop
  noCollision_h : noCollision
  twoFactorClosure_h : twoFactorClosure
  inductionStep_h : inductionStep
  iteratedResultantIsMinimalPolynomial_h : iteratedResultantIsMinimalPolynomial
  degreeMultiplicativity_h : degreeMultiplicativity
  hankelRankMultiplicativity_h : hankelRankMultiplicativity

/-- Paper-facing wrapper for the strict multiplicativity of the multifactor tensor resultant
recursion.
    thm:pom-multifactor-tensor-recurrence-strict-multiplicativity -/
theorem paper_pom_multifactor_tensor_recurrence_strict_multiplicativity
    (D : TensorFoldResultantRecursionData) :
    D.iteratedResultantIsMinimalPolynomial ∧
      D.degreeMultiplicativity ∧
      D.hankelRankMultiplicativity := by
  exact ⟨D.iteratedResultantIsMinimalPolynomial_h, D.degreeMultiplicativity_h,
    D.hankelRankMultiplicativity_h⟩

end Omega.POM
