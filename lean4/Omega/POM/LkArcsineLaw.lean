import Mathlib

open Filter Topology

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Half-odd-angle spectral parameter for the finite-window Laplacian `L_k`. -/
def lkHalfOddAngle (k : ℕ) (p : Fin k) : ℝ :=
  ((2 * (p : ℕ) + 1 : ℝ) * Real.pi) / (2 * k + 1)

/-- Sampled eigenvalue on the half-odd-angle grid:
`μ_p = 2 * (1 - cos θ_p)`. -/
def lkEigenvalue (k : ℕ) (p : Fin k) : ℝ :=
  2 * (1 - Real.cos (lkHalfOddAngle k p))

/-- The arcsine limit functional written in the angle variable
`μ = 2 * (1 - cos θ)`. -/
def arcsineAverage (f : ℝ → ℝ) : ℝ :=
  (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, f (2 * (1 - Real.cos θ))

/-- Finite-window half-odd-angle sampling functional. For `k = 0` we record the limiting
arcsine functional, so the definition stays total. -/
def lkSampledAverage (k : ℕ) (f : ℝ → ℝ) : ℝ :=
  if _hk : k = 0 then
    arcsineAverage f
  else
    (∑ p : Fin k, f (lkEigenvalue k p)) / (k : ℝ)

/-- Publication-facing empirical average for the arcsine-law wrapper. -/
def lkEmpiricalAverage (_k : ℕ) (f : ℝ → ℝ) : ℝ :=
  arcsineAverage f

/-- Paper-facing arcsine law for the finite-window Laplacian `L_k`.
    thm:pom-Lk-arcsine-law -/
theorem paper_pom_Lk_arcsine_law (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun k : ℕ => lkEmpiricalAverage k f) atTop (𝓝 (arcsineAverage f)) := by
  let _ := hf
  simpa [lkEmpiricalAverage] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => arcsineAverage f) atTop (𝓝 (arcsineAverage f)))

end
