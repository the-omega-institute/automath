import Mathlib.Tactic
import Mathlib.Data.Nat.Totient

namespace Omega.Zeta.NecklaceCounting

/-- Binary necklace count for length n. -/
def binaryNecklace (n : ℕ) : ℕ :=
  (Finset.filter (· ∣ n) (Finset.range (n + 1))).sum
    (fun d => Nat.totient d * 2 ^ (n / d)) / n

/-- Binary necklace counting seeds via Burnside/Witt.
    con:xi-terminal-big-witt-functoriality -/
theorem paper_zeta_necklace_counting_seeds :
    (binaryNecklace 1 = 2) ∧ (binaryNecklace 2 = 3) ∧
    (binaryNecklace 3 = 4) ∧ (binaryNecklace 4 = 6) ∧
    (binaryNecklace 5 = 8) ∧ (binaryNecklace 6 = 14) ∧
    (Nat.totient 1 = 1) ∧ (Nat.totient 2 = 1) ∧
    (Nat.totient 3 = 2) ∧ (Nat.totient 4 = 2) ∧
    (Nat.totient 5 = 4) ∧ (Nat.totient 6 = 2) ∧
    (1 * 2 = 1 * 2) ∧
    (2 * 3 = 4 + 2) ∧
    (3 * 4 = 8 + 4) ∧
    (4 * 6 = 16 + 4 + 4) ∧
    (5 * 8 = 32 + 8) ∧
    (6 * 14 = 64 + 8 + 8 + 4) := by
  native_decide

end Omega.Zeta.NecklaceCounting
