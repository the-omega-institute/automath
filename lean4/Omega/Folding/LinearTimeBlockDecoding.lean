import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for linear-time finite-block decoding in the
    rigidity reconstruction section.
    cor:linear-time-block-decoding -/
theorem paper_resolution_folding_linear_time_block_decoding
    (Decodable : ℕ → Prop)
    {m : ℕ}
    (_hm : 3 ≤ m)
    (hInit : Decodable m)
    (hStep : ∀ n, m ≤ n → Decodable n → Decodable (n + 1)) :
    ∀ n, m ≤ n → Decodable n := by
  intro n hn
  rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
  induction k with
  | zero =>
      simpa using hInit
  | succ k ih =>
      have hmk : m ≤ m + k := Nat.le_add_right m k
      have hnext : Decodable (m + k + 1) := hStep (m + k) hmk (ih hmk)
      simpa [Nat.add_assoc] using hnext

end Omega.Folding
