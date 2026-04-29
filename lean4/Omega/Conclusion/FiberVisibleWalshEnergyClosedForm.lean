import Mathlib.Tactic
import Omega.Conclusion.FoldWalshGramSimplexSignatureSection

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

local instance conclusion_fiber_visible_walsh_energy_closed_form_instDecidableEqWord
    (m : ℕ) : DecidableEq (Word m) :=
  Classical.decEq _

local instance conclusion_fiber_visible_walsh_energy_closed_form_instDecidableEqX
    (m : ℕ) : DecidableEq (X m) :=
  Classical.decEq _

/-- Specializing the exact Gram law to `x = y` identifies the total nonempty Walsh energy of a
single fiber with the closed form `d_m(x) (2^m - d_m(x))`. -/
theorem paper_conclusion_fiber_visible_walsh_energy_closed_form
    (m : ℕ) (x : X m) :
    ∑ I ∈ nonemptySubsets m, walshProfile m x I ^ 2 =
      (X.fiberMultiplicity x : ℝ) * ((2 : ℝ) ^ m - (X.fiberMultiplicity x : ℝ)) := by
  calc
    ∑ I ∈ nonemptySubsets m, walshProfile m x I ^ 2
        = (2 : ℝ) ^ m * (X.fiberMultiplicity x : ℝ) -
            (X.fiberMultiplicity x : ℝ) * (X.fiberMultiplicity x : ℝ) := by
            simpa [pow_two] using paper_conclusion_fold_nontrivial_walsh_exact_gram_law m x x
    _ = (X.fiberMultiplicity x : ℝ) * ((2 : ℝ) ^ m - (X.fiberMultiplicity x : ℝ)) := by
          ring

end

end Omega.Conclusion
