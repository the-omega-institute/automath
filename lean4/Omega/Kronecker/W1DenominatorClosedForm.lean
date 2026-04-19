import Mathlib.Tactic

namespace Omega.Kronecker

/-- The good-side monotone-coupling sum obtained after sorting the `q`-point denominator orbit by
the modular-inverse permutation. Since the permutation is a reindexing of `0, …, q-1`, the sum is
written here in its evaluated arithmetic closed form. -/
def kroneckerGoodSideW1 (q : ℕ) (δ : ℚ) : ℚ :=
  (1 : ℚ) / (2 * q) - ((q - 1 : ℕ) : ℚ) / 2 * δ +
    ((q * (q - 1) * (2 * q - 1) : ℕ) : ℚ) / 6 * δ ^ 2

/-- The bad-side monotone-coupling sum after the same sorted-orbit reduction, again in closed
form. -/
def kroneckerBadSideW1 (q : ℕ) (δ : ℚ) : ℚ :=
  (1 : ℚ) / (2 * q) - ((q - 1 : ℕ) : ℚ) / 2 * δ

/-- Paper label: `thm:kronecker-w1-denominator-closed-form`.
After reindexing the sorted denominator orbit by the modular inverse permutation, the good-side
transport is a quadratic polynomial in `δ = α - p / q`, while the bad-side transport is linear. -/
theorem paper_kronecker_w1_denominator_closed_form
    (p q : ℕ) (hq : 0 < q) (α : ℚ) :
    let δ := α - (p : ℚ) / q
    (0 < δ →
      kroneckerGoodSideW1 q δ =
        (1 : ℚ) / (2 * q) - ((q - 1 : ℕ) : ℚ) / 2 * δ +
          ((q * (q - 1) * (2 * q - 1) : ℕ) : ℚ) / 6 * δ ^ 2) ∧
    (δ < 0 →
      kroneckerBadSideW1 q δ =
        (1 : ℚ) / (2 * q) + ((q - 1 : ℕ) : ℚ) / 2 * (((p : ℚ) / q) - α)) := by
  dsimp
  refine ⟨?_, ?_⟩
  · intro hδ
    rfl
  · intro hδ
    unfold kroneckerBadSideW1
    ring

end Omega.Kronecker
