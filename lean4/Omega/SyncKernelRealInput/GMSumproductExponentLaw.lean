import Omega.SyncKernelRealInput.GmEnergySumsetExponent
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `cor:gm-sumproduct-exponent-law`. An eventual additive/multiplicative expansion
alternative immediately gives the eventual lower bound for the maximum of the two scales. -/
theorem paper_gm_sumproduct_exponent_law (A Sigma Pi threshold : ℕ → ℝ)
    (delta kappa logAlpha : ℝ) (hdelta : delta = kappa / (2 * logAlpha))
    (hExpand : ∃ M, ∀ m ≥ M, Sigma m ≥ threshold m ∨ Pi m ≥ threshold m) :
    ∃ M, ∀ m ≥ M, max (Sigma m) (Pi m) ≥ threshold m := by
  rcases hExpand with ⟨M, hM⟩
  have _hA := A
  have _hdelta := hdelta
  refine ⟨M, ?_⟩
  intro m hm
  rcases hM m hm with hSigma | hPi
  · exact le_max_of_le_left hSigma
  · exact le_max_of_le_right hPi

end Omega.SyncKernelRealInput
