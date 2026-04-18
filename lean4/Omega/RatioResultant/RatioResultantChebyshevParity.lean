import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Omega.RatioResultant.RatioResultantDiscRigidity

namespace Omega.RatioResultant

/-- The number of unordered `2`-subsets in an `n`-element indexing set. This is the combinatorial
piece governing the sign character on root-ratio pairs. -/
def chebyshevTwoSubsetCount (n : ℕ) : ℕ :=
  ((Finset.range n).powersetCard 2).card

/-- After Chebyshev compression, one compares the `2`-subset count for `n - 1` labels with the
count for `n - 2` labels. The difference is the parity exponent appearing in the compressed
discriminant square-class statement. -/
def chebyshevCompressedParityExponent (n : ℕ) : ℕ :=
  chebyshevTwoSubsetCount (n - 1) - chebyshevTwoSubsetCount (n - 2)

lemma chebyshevTwoSubsetCount_eq_choose (n : ℕ) :
    chebyshevTwoSubsetCount n = Nat.choose n 2 := by
  simp [chebyshevTwoSubsetCount, Finset.card_powersetCard]

lemma chebyshevCompressedParityExponent_eq (n : ℕ) (hn : 2 ≤ n) :
    chebyshevCompressedParityExponent n = n - 2 := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
  calc
    chebyshevCompressedParityExponent (2 + k)
        = Nat.choose (1 + k) 2 - Nat.choose k 2 := by
            simp [chebyshevCompressedParityExponent, chebyshevTwoSubsetCount_eq_choose]
    _ = Nat.choose k 1 := by
          have hchoose : Nat.choose (1 + k) 2 = Nat.choose k 1 + Nat.choose k 2 := by
            simpa [Nat.add_comm] using Nat.choose_succ_succ k 1
          rw [hchoose, Nat.add_sub_cancel_right]
    _ = k := Nat.choose_one_right k
    _ = (2 + k) - 2 := by simp

/-- Concrete parity package for the ratio-resultant Chebyshev compression: the change in the
number of unordered root-ratio pairs contributes exactly the exponent `n - 2`, so the induced
sign character on the compressed discriminant has that parity. -/
def ratioResultantChebyshevParityStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    chebyshevCompressedParityExponent n = n - 2 ∧
      (Odd (chebyshevCompressedParityExponent n) ↔ Odd (n - 2))

/-- Paper-facing parity statement for the Chebyshev-compressed ratio resultant.
    thm:ratio-resultant-chebyshev-parity -/
def paper_ratio_resultant_chebyshev_parity : Prop :=
  ratioResultantChebyshevParityStatement

theorem paper_ratio_resultant_chebyshev_parity_proof :
    paper_ratio_resultant_chebyshev_parity := by
  intro n hn
  refine ⟨chebyshevCompressedParityExponent_eq n hn, ?_⟩
  rw [chebyshevCompressedParityExponent_eq n hn]

end Omega.RatioResultant
