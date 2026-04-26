import Mathlib.Tactic

namespace Omega.Conclusion.FoldbinRemainderFaithfulCompressionRateOne

/-- Positive multiplicities cannot compress the total block dimension below rate one. -/
theorem paper_conclusion_foldbin_remainder_faithful_compression_rate_one {ι : Type*}
    [Fintype ι] (blockDim : ι → ℕ) (hpos : ∀ i, 0 < blockDim i) :
    (∃ multiplicity : ι → ℕ,
        (∀ i, 0 < multiplicity i) ∧
          (∑ i, multiplicity i * blockDim i) = ∑ i, blockDim i) ∧
      ∀ multiplicity : ι → ℕ,
        (∀ i, 0 < multiplicity i) →
          (∑ i, blockDim i) ≤ ∑ i, multiplicity i * blockDim i := by
  have foldbin_remainder_faithful_compression_rate_one_block_pos : ∀ i, 0 < blockDim i :=
    hpos
  constructor
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · intro i
      exact Nat.zero_lt_one
    · simp
  · intro multiplicity hmult
    refine Finset.sum_le_sum ?_
    intro i _hi
    have _ : 0 < blockDim i :=
      foldbin_remainder_faithful_compression_rate_one_block_pos i
    exact Nat.le_mul_of_pos_left (blockDim i) (hmult i)

end Omega.Conclusion.FoldbinRemainderFaithfulCompressionRateOne
