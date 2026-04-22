import Omega.Zeta.XiCayleyJoukowskyHarmonicMeasureEllipse

namespace Omega.Zeta

theorem paper_xi_critical_line_circle_cauchy_uniformization (θ : ℝ) :
    let t : ℝ := (1 / 2) * Real.tan (θ / 2)
    let x : ℝ := 2 * t
    xiUniformAngleDensityFromCayley x = xiCauchyDensity x := by
  simpa using
    (paper_xi_cayley_joukowsky_harmonic_measure_ellipse.1
      (((2 : ℝ) * ((1 / 2 : ℝ) * Real.tan (θ / 2)))))

end Omega.Zeta
