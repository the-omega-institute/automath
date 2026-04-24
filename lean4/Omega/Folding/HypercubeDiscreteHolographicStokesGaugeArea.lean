import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Paper label: `prop:hypercube-discrete-holographic-stokes-gauge-area`.

If the averaged factorial lower bound is controlled by a fiberwise logarithmic term and that
logarithmic term is itself bounded below by the hypercube edge-isoperimetric contribution, then
the normalized gauge volume density is bounded from below by the displayed area law. -/
theorem paper_hypercube_discrete_holographic_stokes_gauge_area
    (n : ℕ) (g area imageCard fiberLogAverage : ℝ)
    (hfactorial :
      fiberLogAverage - 1 + imageCard / (2 : ℝ) ^ n ≤ g)
    (hisoper :
      (n : ℝ) * Real.log 2 - 2 * Real.log 2 * area / (2 : ℝ) ^ n ≤ fiberLogAverage) :
    (n : ℝ) * Real.log 2 - 1 - 2 * Real.log 2 * area / (2 : ℝ) ^ n +
        imageCard / (2 : ℝ) ^ n ≤
      g := by
  linarith

end Omega.Folding
