import Mathlib.Tactic
import Omega.Folding.BlockFoldsatNpComplete

namespace Omega.Folding

/-- Paper label: `thm:block-foldsat-constant-precision-hardness`.
Once the audited Block--FoldSAT package is available, any boundary functional that separates the
unsatisfiable instances at value `1` from the satisfiable ones at value at least `2` has the
constant threshold `3/2`; a uniform additive error `< 1/4` would therefore decide the underlying
hard predicate. -/
theorem paper_block_foldsat_constant_precision_hardness :
    ∀ (D : BlockFoldsatNpCompleteData) {Hard Family : Type*}
      (hardPred : Hard → Prop) (encode : Hard → Family) (expectationNorm : Family → ℚ)
      (hUnsat : ∀ x, ¬ hardPred x → expectationNorm (encode x) = 1)
      (hSat : ∀ x, hardPred x → (2 : ℚ) ≤ expectationNorm (encode x))
      (hHardUndecidable : ¬ Nonempty (∀ x, Decidable (hardPred x))),
      ∃ τ : ℚ,
        τ = 3 / 2 ∧
          D.npComplete ∧
          (∀ x, expectationNorm (encode x) > τ ↔ hardPred x) ∧
          ¬ ∃ approx : Family → ℚ, ∀ y : Family, |expectationNorm y - approx y| < 1 / 4 := by
  intro D Hard Family hardPred encode expectationNorm hUnsat hSat hHardUndecidable
  refine ⟨3 / 2, rfl, (paper_block_foldsat_np_complete D).2.2, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      by_contra hNotHard
      rw [hUnsat x hNotHard] at hx
      norm_num at hx
    · intro hx
      have hLower : (2 : ℚ) ≤ expectationNorm (encode x) := hSat x hx
      linarith
  · intro hApprox
    rcases hApprox with ⟨approx, hApprox⟩
    apply hHardUndecidable
    refine ⟨?_⟩
    intro x
    by_cases hx : approx (encode x) > (3 / 2 : ℚ)
    · refine isTrue ?_
      by_contra hNotHard
      have hClose : |expectationNorm (encode x) - approx (encode x)| < (1 / 4 : ℚ) :=
        hApprox (encode x)
      rw [hUnsat x hNotHard] at hClose
      have hBounds := abs_lt.mp hClose
      linarith
    · refine isFalse ?_
      intro hHard
      have hClose : |expectationNorm (encode x) - approx (encode x)| < (1 / 4 : ℚ) :=
        hApprox (encode x)
      have hBounds := abs_lt.mp hClose
      have hx' : approx (encode x) ≤ (3 / 2 : ℚ) := by linarith
      have hLower : (2 : ℚ) ≤ expectationNorm (encode x) := hSat x hHard
      linarith

end Omega.Folding
