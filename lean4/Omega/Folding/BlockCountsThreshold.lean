import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the exact block-count corollary above the
    reconstruction threshold.
    cor:block-counts-threshold -/
theorem paper_resolution_folding_block_counts_threshold
    {BlockLanguage RawBlocks : Type}
    [Fintype BlockLanguage] [Fintype RawBlocks]
    (B : BlockLanguage ≃ RawBlocks)
    (m n : ℕ)
    (_hm : 3 ≤ m)
    (_hn : m ≤ n)
    (hRawCard : Fintype.card RawBlocks = 2 ^ (n + m - 1)) :
    Fintype.card BlockLanguage = 2 ^ (n + m - 1) ∧
      (n = m → Fintype.card BlockLanguage = 2 ^ (2 * m - 1)) := by
  have hCard : Fintype.card BlockLanguage = 2 ^ (n + m - 1) := by
    calc
      Fintype.card BlockLanguage = Fintype.card RawBlocks := Fintype.card_congr B
      _ = 2 ^ (n + m - 1) := hRawCard
  refine ⟨hCard, ?_⟩
  intro hnm
  subst hnm
  simpa [two_mul, Nat.add_assoc] using hCard

end Omega.Folding
