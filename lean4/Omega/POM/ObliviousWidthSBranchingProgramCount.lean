import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.POM

/-- Lean-side description count for width-`S` oblivious branching programs on `m` input layers:
for each layer and each state, the `0`- and `1`-transitions choose one of `S` successor states. -/
abbrev obliviousWidthSTransitionTableCount (m S : Nat) : Nat :=
  Fintype.card (Fin m → Bool → Fin S → Fin S)

/-- The terminal output map sends each of the `S` states to one of `n` output values. -/
abbrev obliviousWidthSOutputMapCount (S n : Nat) : Nat :=
  Fintype.card (Fin S → Fin n)

/-- The number of concrete width-`S` oblivious branching-program descriptions obtained by choosing
all transition tables and the terminal output map. This description count is the explicit finite
upper bound used for the paper-facing realizability estimate. -/
abbrev obliviousWidthSFunctionCount (m S n : Nat) : Nat :=
  obliviousWidthSOutputMapCount S n * obliviousWidthSTransitionTableCount m S

private theorem obliviousWidthSOutputMapCount_eq (S n : Nat) :
    obliviousWidthSOutputMapCount S n = n ^ S := by
  unfold obliviousWidthSOutputMapCount
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

private theorem obliviousWidthSTransitionTableCount_eq (m S : Nat) :
    obliviousWidthSTransitionTableCount m S = S ^ (2 * S * m) := by
  unfold obliviousWidthSTransitionTableCount
  rw [Fintype.card_fun]
  have hinner : Fintype.card (Bool → Fin S → Fin S) = S ^ (2 * S) := by
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.mul_comm] using
      (Nat.pow_mul S S 2).symm
  rw [hinner, Fintype.card_fin]
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (Nat.pow_mul S (2 * S) m).symm

/-- Paper label: `thm:pom-oblivious-widthS-branching-program-count`.
Counting the `S^(2S)` transition choices per layer over `m` layers and the `n^S` terminal output
maps gives the advertised upper bound on the realizable-function count. -/
theorem paper_pom_oblivious_widthS_branching_program_count (m S n : Nat) :
    obliviousWidthSFunctionCount m S n <= n ^ S * S ^ (2 * S * m) := by
  rw [obliviousWidthSFunctionCount, obliviousWidthSOutputMapCount_eq,
    obliviousWidthSTransitionTableCount_eq]

/-- Lowercase paper-label wrapper for
`thm:pom-oblivious-widthS-branching-program-count`. -/
theorem paper_pom_oblivious_widths_branching_program_count (m S n : Nat) :
    obliviousWidthSFunctionCount m S n <= n ^ S * S ^ (2 * S * m) := by
  exact paper_pom_oblivious_widthS_branching_program_count m S n

end Omega.POM
