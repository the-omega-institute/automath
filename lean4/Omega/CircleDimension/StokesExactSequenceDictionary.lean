import Mathlib.Tactic
import Omega.CircleDimension.StokesHomologyExactSplitting

namespace Omega.CircleDimension

open Omega.CircleDimension.StokesHomologyExactSplitting

/-- Paper-facing dictionary between the low-dimensional Stokes long exact sequence and its split
coordinate model.
    prop:cdim-stokes-exact-sequence-dictionary -/
theorem paper_cdim_stokes_exact_sequence_dictionary (u v : ℕ) :
    Function.Injective (stokesBoundaryInclusion u v) ∧
      Function.Surjective (stokesProjection u v) ∧
      Set.range (stokesBoundaryInclusion u v) = {p | stokesProjection u v p = 0} ∧
      (∀ p,
        stokesSection u v (stokesProjection u v p) + stokesBoundaryInclusion u v p.2 = p) := by
  rcases paper_cdim_stokes_homology_exact_splitting_seeds u v with
    ⟨hInj, hSurj, hRange, _, hDecomp⟩
  exact ⟨hInj, hSurj, hRange, hDecomp⟩

end Omega.CircleDimension
