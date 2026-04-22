import Omega.OperatorAlgebra.CircuitNoninjectiveNPComplete
import Omega.OperatorAlgebra.FoldWatataniIndexMultiplicityField

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

theorem paper_circuit_condexp_index_maxfiber {n : ℕ} (C : BoolCircuit n) :
    let D := Finset.univ.sup fun y => Fintype.card (FoldJonesBasicConstructionDirectsum.foldFiber C y)
    Finset.univ.sup (fun y => Omega.OperatorAlgebra.foldWatataniIndexElement C y) = D := by
  classical
  simp [foldWatataniIndexElement, foldWatataniIndexCoefficient]

end Omega.OperatorAlgebra
