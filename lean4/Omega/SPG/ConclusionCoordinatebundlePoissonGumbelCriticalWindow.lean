import Mathlib.Data.Real.Basic

namespace Omega.SPG

/-- The probability that a single `d`-coordinate layer is missed by independent sampling at
coordinate rate `p`. -/
def conclusion_coordinatebundle_poisson_gumbel_critical_window_missedLayerProbability
    (d : ℕ) (p : ℝ) : ℝ :=
  (1 - p) ^ d

/-- The probability that a single layer is hit at least once. -/
def conclusion_coordinatebundle_poisson_gumbel_critical_window_hitLayerProbability
    (d : ℕ) (p : ℝ) : ℝ :=
  1 - conclusion_coordinatebundle_poisson_gumbel_critical_window_missedLayerProbability d p

/-- Exact finite product probability for all `L` independent coordinate layers to be hit. -/
def conclusion_coordinatebundle_poisson_gumbel_critical_window_exactificationProbability
    (L d : ℕ) (p : ℝ) : ℝ :=
  (conclusion_coordinatebundle_poisson_gumbel_critical_window_hitLayerProbability d p) ^ L

/-- Paper label: `thm:conclusion-coordinatebundle-poisson-gumbel-critical-window`. -/
theorem paper_conclusion_coordinatebundle_poisson_gumbel_critical_window (L d : ℕ) (p : ℝ) :
    conclusion_coordinatebundle_poisson_gumbel_critical_window_exactificationProbability L d p =
      (1 - (1 - p) ^ d) ^ L := by
  rfl

end Omega.SPG
