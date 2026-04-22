import Omega.Folding.FixedFiberLedgerComplexity

namespace Omega

/-- The distinguished fixed word `x⋆_{3n}` represented blockwise by the constant `100` block. -/
def foldFibreStarTargetWord (n : ℕ) : FoldFibreStarWord n :=
  fun _ => foldFibreStarTargetBlock

private lemma foldFibreStarTargetWord_weight (n : ℕ) :
    foldFibreStarWeight (foldFibreStarTargetWord n) = foldFibreStarTargetWeight n := by
  simpa [foldFibreStarTargetWord, foldFibreStarTargetBlock, foldFibreStarEncode,
    foldFibreStarEncodeBlock] using
    foldFibreStarEncode_weight (n := n) (fun _ => false)

/-- Paper label: `thm:fold-fixed-fiber-kolmogorov-collapse`.
The explicit `100/011` encoder sends every source word to the same fixed target word in the
`3n`-block fiber, the fiber already contains at least `2^n` points, and the associated
one-point ledger model has entropy exactly `n log 2`. -/
theorem paper_fold_fixed_fiber_kolmogorov_collapse :
    (∀ n (w : FoldFibreStarBitstring n),
      foldFibreStarWeight (foldFibreStarEncode w) =
        foldFibreStarWeight (foldFibreStarTargetWord n)) ∧
    (∀ n, 2 ^ n ≤ foldFibreStarMultiplicity n) ∧
    (∀ n,
      Real.log (((Finset.univ.image (foldFibreStarEncode (n := n))).card : ℝ)) = n * Real.log 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n w
    rw [foldFibreStarEncode_weight, foldFibreStarTargetWord_weight]
  · exact paper_fold_fibre_star_exp_lb
  · intro n
    rw [foldFibreStarImage_card, foldFibreStar_log_two_pow]

end Omega
