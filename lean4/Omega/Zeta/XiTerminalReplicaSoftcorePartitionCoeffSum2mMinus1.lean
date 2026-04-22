import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

namespace Omega.Zeta

/-- The paper's partition-coefficient sum: all length-`m` `{J,K}`-words, excluding the unique
all-`K` word. Encoding `J/K` by `Bool` makes this the total binary-word count minus one. -/
def xi_terminal_replica_softcore_partition_coeff_sum_2m_minus_1_sum (m : ℕ) : ℕ :=
  Fintype.card (Fin m → Bool) - 1

/-- The partition-coefficient sum equals the number of non-all-`K` binary words of length `m`,
namely `2^m - 1`.
    cor:xi-terminal-replica-softcore-partition-coeff-sum-2m-minus-1 -/
theorem paper_xi_terminal_replica_softcore_partition_coeff_sum_2m_minus_1 (m : ℕ) :
    xi_terminal_replica_softcore_partition_coeff_sum_2m_minus_1_sum m = 2 ^ m - 1 := by
  rw [xi_terminal_replica_softcore_partition_coeff_sum_2m_minus_1_sum, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

end Omega.Zeta
