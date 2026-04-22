import Mathlib.Tactic
import Omega.POM.FiberSpectrumPronyHankelRank
import Omega.POM.FiberSpectrumPronyHankelThresholdSharp

namespace Omega.POM

/-- The audited power-sum window length attached to an `R`-atom fiber spectrum. -/
def pom_fiber_spectrum_finite_reconstruction_sharp_window (R : ℕ) : ℕ :=
  2 * R

/-- Concrete reconstruction package extracted from the Hankel-rank and recurrence-order
identification. -/
def pom_fiber_spectrum_finite_reconstruction_sharp_reconstructs
    (D : FiberSpectrumPronyHankelRankData) : Prop :=
  D.atomCount = D.hankelRank ∧ D.atomCount = D.minimalRecurrenceOrder

/-- Paper label: `thm:pom-fiber-spectrum-finite-reconstruction-sharp`. The first `2R` power sums
recover the finite fiber spectrum through the Prony/Hankel rank package, and the sharp-threshold
gap shows that dropping the last moment leaves a generic ambiguity witness. -/
theorem paper_pom_fiber_spectrum_finite_reconstruction_sharp
    (D : FiberSpectrumPronyHankelRankData) (hR : 2 ≤ D.atomCount) :
    pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount = 2 * D.atomCount ∧
      pom_fiber_spectrum_finite_reconstruction_sharp_reconstructs D ∧
      (∀ k : ℕ, k ≤ pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount - 2 →
        pomPronyHankelThresholdGap D.atomCount k = 0) ∧
      pomPronyHankelThresholdGap D.atomCount
          (pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount - 1) =
        Nat.factorial
          (pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount - 1) := by
  have hReconstruct := paper_pom_fiber_spectrum_prony_hankel_rank D
  have hSharp := paper_pom_fiber_spectrum_prony_hankel_threshold_sharp D.atomCount hR
  refine ⟨rfl, hReconstruct, ?_, ?_⟩
  · intro k hk
    exact hSharp.1 k (by simpa [pom_fiber_spectrum_finite_reconstruction_sharp_window] using hk)
  · simpa [pom_fiber_spectrum_finite_reconstruction_sharp_window] using hSharp.2

end Omega.POM
