import Mathlib.Tactic
import Omega.OperatorAlgebra.CircuitS2SharpPComplete
import Omega.OperatorAlgebra.FoldWatataniIndexMoments

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum
open scoped BigOperators

/-- The circuit collision moment written in the same blockwise coordinates as the Watatani index
field. -/
def circuit_watatani_moments_sharpp_complete_collision_moment {n : ℕ} (C : BoolCircuit n)
    (q : ℕ) : ℚ :=
  ∑ y, (Fintype.card (foldFiber C y) : ℚ) ^ q

/-- Concrete wrapper for the circuit collision-moment / Watatani-moment identification together
with the fixed-`q` sharpP package already formalized elsewhere. -/
def circuit_watatani_moments_sharpp_complete_statement (q : ℕ) : Prop :=
  (∀ {n : ℕ} (C : BoolCircuit n),
      (2 ^ n : ℚ) * foldWatataniTracedIndexMoment C (q - 1) =
        circuit_watatani_moments_sharpp_complete_collision_moment C q) ∧
    circuit_s2_sharpp_complete_claim q

/-- Paper label: `cor:circuit-watatani-moments-sharpP-complete`. -/
theorem paper_circuit_watatani_moments_sharpp_complete (q : ℕ) (hq : 2 ≤ q) :
    circuit_watatani_moments_sharpp_complete_statement q := by
  refine ⟨?_, paper_circuit_s2_sharpp_complete q hq⟩
  intro n C
  have hcard : Fintype.card (BitVec n) = 2 ^ n := by
    simp [BitVec]
  have hqpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
  have hqsplit : q - 1 + 1 = q := Nat.succ_pred_eq_of_pos hqpos
  have hmoment := (paper_op_algebra_fold_watatani_index_moments C n (q - 1) hcard).2.2
  calc
    (2 ^ n : ℚ) * foldWatataniTracedIndexMoment C (q - 1)
      = (2 ^ n : ℚ) *
          ((∑ y, (Fintype.card (foldFiber C y) : ℚ) ^ q) / 2 ^ n) := by
            rw [hmoment, hqsplit]
    _ = circuit_watatani_moments_sharpp_complete_collision_moment C q := by
      unfold circuit_watatani_moments_sharpp_complete_collision_moment
      have hpow : (2 ^ n : ℚ) ≠ 0 := by
        positivity
      field_simp [hpow]

end Omega.OperatorAlgebra
