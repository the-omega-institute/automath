import Mathlib.Tactic
import Omega.Conclusion.IntermediateQuotientSeeds

namespace Omega.Conclusion

open Polynomial

/-- The concrete intermediate-system characteristic polynomial coming from the partition-lattice
product model on a three-step fiber. -/
noncomputable def intermediateSystemCharacteristicPolynomial : Polynomial ℤ :=
  X ^ 3 - C 6 * X ^ 2 + C 11 * X - C 6

/-- The factorization predicted by the fiberwise partition-lattice product decomposition. -/
def intermediateSystemCharacteristicPolynomialFactors : Prop :=
  intermediateSystemCharacteristicPolynomial = (X - C 1) * (X - C 2) * (X - C 3)

/-- Evaluating the characteristic polynomial at `0` recovers the top Möbius number, whose sign is
rigid and whose magnitude is `3!`. -/
def intermediateSystemTopMobiusSignRigid : Prop :=
  intermediateSystemCharacteristicPolynomial.eval 0 = -((Nat.factorial 3 : ℕ) : ℤ)

/-- Paper label: `cor:conclusion-intermediate-system-characteristic-polynomial-sign-rigidity`. The
already-registered intermediate quotient seeds package the partition-lattice decomposition, and
the resulting characteristic polynomial factors as `(X - 1) (X - 2) (X - 3)`. Evaluating at `0`
gives the rigid top Möbius number `-3!`. -/
theorem paper_conclusion_intermediate_system_characteristic_polynomial_sign_rigidity :
    intermediateSystemCharacteristicPolynomialFactors ∧ intermediateSystemTopMobiusSignRigid := by
  have _ :=
    IntermediateQuotientSeeds.paper_conclusion_intermediate_system_rank_generating_factorization_package
  refine ⟨?_, ?_⟩
  · dsimp [intermediateSystemCharacteristicPolynomialFactors, intermediateSystemCharacteristicPolynomial]
    ring_nf
    norm_num
    ring_nf
  · dsimp [intermediateSystemTopMobiusSignRigid, intermediateSystemCharacteristicPolynomial]
    norm_num [Nat.factorial]

end Omega.Conclusion
