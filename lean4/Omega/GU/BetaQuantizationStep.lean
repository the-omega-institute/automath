import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.GU

/-- Integer-layer wrapper for the irreducible beta quantization step.
    prop:beta-quantization-step -/
theorem paper_gut_beta_quantization_step {ι : Type} (beta : ι → Real) (w : ι → Int) (base : Real)
    (hbeta :
      ∀ i, beta i = base + (w i : Real) * Real.log (2 / Real.goldenRatio)) :
    ∀ i j, ∃ k : Int,
      beta i - beta j = (k : Real) * Real.log (2 / Real.goldenRatio) := by
  intro i j
  refine ⟨w i - w j, ?_⟩
  calc
    beta i - beta j =
        (base + (w i : Real) * Real.log (2 / Real.goldenRatio)) -
          (base + (w j : Real) * Real.log (2 / Real.goldenRatio)) := by
            rw [hbeta i, hbeta j]
    _ = ((w i : Real) - (w j : Real)) * Real.log (2 / Real.goldenRatio) := by ring
    _ = ((w i - w j : Int) : Real) * Real.log (2 / Real.goldenRatio) := by
      rw [Int.cast_sub]

end Omega.GU
