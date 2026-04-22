import Mathlib.Data.Fintype.Card
import Omega.OperatorAlgebra.CircuitNoninjectiveNPComplete
import Omega.OperatorAlgebra.NpWatataniIndexSupportCharacterization

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

/-- Paper label: `cor:index-support-sat-np-hard-index-coeff-sharpP`. The SAT verifier on a dummy
input has a single projector whose Watatani-index coefficient is exactly the number of satisfying
assignments, so support nonemptiness is satisfiability and coefficient extraction is `#SAT`. -/
def paper_index_support_sat_np_hard_index_coeff_sharpp : Prop := by
  exact
    ∀ {n : ℕ} (φ : BitVec n → Bool),
      let paper_index_support_sat_np_hard_index_coeff_sharpp_sat_verifier :
          Unit → BitVec n → Bool := fun _ w => φ w
      foldWatataniIndexElement
          (verifierFold paper_index_support_sat_np_hard_index_coeff_sharpp_sat_verifier) () =
        Fintype.card {w : BitVec n // φ w = true} ∧
        (verifierProjectorInSupport paper_index_support_sat_np_hard_index_coeff_sharpp_sat_verifier
            () ↔ satisfiable φ)

end Omega.OperatorAlgebra
