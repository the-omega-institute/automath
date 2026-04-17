import Omega.CircleDimension.StokesExactSequenceDictionary
import Omega.CircleDimension.WdimSignedCircleDimension

namespace Omega.CircleDimension

open Omega.CircleDimension.StokesHomologyExactSplitting

/-- Bookkeeping rank of `H¹(X₀(M))` in the split Stokes model. -/
def stokesH1Rank (u _v : ℕ) : ℕ := u

/-- Bookkeeping rank of the relative `H²(X₀(M), Σ₀(M))` term in the split Stokes model. -/
def stokesRelativeH2Rank (_u v : ℕ) : ℕ := v

/-- Boundary torus rank for `Σ₀(M)` in the orthant/Stokes dictionary. -/
def stokesSigma0Rank (u v : ℕ) : ℕ := u + v

/-- The split Stokes exact-sequence model identifies the cohomological ranks with the orthant
parameters `(u, v)`, and the resulting weighted/signed circle dimensions agree with the closed
form `u + v/2`. -/
theorem paper_cdim_signed_stokes_cohomological_characterization (u v : ℕ) :
    Function.Injective (stokesBoundaryInclusion u v) ∧
      Function.Surjective (stokesProjection u v) ∧
      Set.range (stokesBoundaryInclusion u v) = {p | stokesProjection u v p = 0} ∧
      (∀ p, stokesSection u v (stokesProjection u v p) + stokesBoundaryInclusion u v p.2 = p) ∧
      stokesH1Rank u v = u ∧
      stokesRelativeH2Rank u v = v ∧
      stokesSigma0Rank u v = u + v ∧
      wdim (u : ℚ) (v : ℚ) = cdimSigned u v 0 0 ∧
      cdimSigned u v 0 0 = (u : ℚ) + (v : ℚ) / 2 := by
  rcases paper_cdim_stokes_exact_sequence_dictionary u v with ⟨hInj, hSurj, hRange, hSplit⟩
  refine ⟨hInj, hSurj, hRange, hSplit, rfl, rfl, rfl, ?_, ?_⟩
  · exact paper_cdim_stokes_character_contraction_general_monoid u v
  · simpa [cdimSignedOrthant] using (paper_cdim_signed_orthant_closed.1 u v 0)

end Omega.CircleDimension
