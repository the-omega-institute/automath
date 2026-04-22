import Mathlib.Tactic
import Omega.Core.PowerInequality
import Omega.OperatorAlgebra.DerivedCoarseningGenusSignLaw

namespace Omega.DerivedConsequences

open Omega.OperatorAlgebra

/-- Paper label: `cor:derived-coarsening-strictly-increases-qfold-environment-rank`.
For a genuine merge step with positive class sizes, the `q`-power rank strictly increases for every
`q > 1`. -/
theorem paper_derived_coarsening_strictly_increases_qfold_environment_rank {OmegaTy : Type*}
    [Fintype OmegaTy] [DecidableEq OmegaTy]
    (D : Omega.OperatorAlgebra.DerivedCoarseningGenusSignLawData OmegaTy) {q : ℕ} (hq : 1 < q) :
    D.left.card ^ q + D.right.card ^ q < D.mergedCard ^ q := by
  have hleft_pos_nat : 0 < D.left.card := Finset.card_pos.mpr D.left_nonempty
  have hright_pos_nat : 0 < D.right.card := Finset.card_pos.mpr D.right_nonempty
  have hq' : 2 ≤ q := by omega
  have hsuper :
      D.left.card ^ q + D.right.card ^ q + 1 ≤ (D.left.card + D.right.card) ^ q := by
    exact Omega.pow_add_strict_super D.left.card D.right.card q
      (Nat.succ_le_of_lt hleft_pos_nat) (Nat.succ_le_of_lt hright_pos_nat) hq'
  rw [show D.mergedCard = D.left.card + D.right.card by rfl]
  omega

end Omega.DerivedConsequences
