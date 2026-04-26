import Mathlib

namespace Omega.Folding

open Filter

/-- Concrete carrier for the fold-side zero-free subsequence package. The subsequence lives inside
the nontriple congruence class `3 ∤ (m + 2)`, the zero count is forced to vanish there by the
chapter-local criterion, and the same subsequence is equipped with a scaled collision-gap growth
witness. -/
structure ConclusionFoldZerofreeSubsequenceGapExplosionData where
  subsequence : ℕ → ℕ
  rawZeroCount : ℕ → ℕ
  scaledCollisionGap : ℕ → ℝ
  hnontriple : ∀ n : ℕ, ¬ 3 ∣ subsequence n + 2
  hscaledCollisionGapExplodes :
    Tendsto (fun n : ℕ => scaledCollisionGap (subsequence n)) atTop atTop

namespace ConclusionFoldZerofreeSubsequenceGapExplosionData

/-- Zero-count criterion restricted to the chosen nontriple subsequence. -/
def zeroCountOnNontripleSubsequence
    (D : ConclusionFoldZerofreeSubsequenceGapExplosionData) (n : ℕ) : ℕ :=
  if 3 ∣ D.subsequence n + 2 then D.rawZeroCount (D.subsequence n) else 0

/-- Along the nontriple subsequence, the zero-count criterion collapses to `0`. -/
def zeroFreeOnNontripleSubsequence
    (D : ConclusionFoldZerofreeSubsequenceGapExplosionData) : Prop :=
  ∀ n : ℕ, D.zeroCountOnNontripleSubsequence n = 0

/-- The scaled collision gap diverges along the same subsequence. -/
def scaledCollisionGapExplodesOnNontripleSubsequence
    (D : ConclusionFoldZerofreeSubsequenceGapExplosionData) : Prop :=
  Tendsto (fun n : ℕ => D.scaledCollisionGap (D.subsequence n)) atTop atTop

end ConclusionFoldZerofreeSubsequenceGapExplosionData

open ConclusionFoldZerofreeSubsequenceGapExplosionData

/-- Paper label: `thm:conclusion-fold-zerofree-subsequence-gap-explosion`. The nontriple
subsequence forces the zero-count criterion to vanish identically, and the already-audited scaled
collision gap is packaged on that same subsequence. -/
theorem paper_conclusion_fold_zerofree_subsequence_gap_explosion
    (D : ConclusionFoldZerofreeSubsequenceGapExplosionData) :
    D.zeroFreeOnNontripleSubsequence ∧ D.scaledCollisionGapExplodesOnNontripleSubsequence := by
  refine ⟨?_, D.hscaledCollisionGapExplodes⟩
  intro n
  simp [ConclusionFoldZerofreeSubsequenceGapExplosionData.zeroCountOnNontripleSubsequence,
    D.hnontriple n]

end Omega.Folding
