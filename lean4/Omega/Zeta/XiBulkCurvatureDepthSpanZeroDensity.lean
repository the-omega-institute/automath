import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete exponential-polynomial endpoint data for the Cartwright indicator abstraction. -/
structure xi_bulk_curvature_depth_span_zero_density_data where
  xi_bulk_curvature_depth_span_zero_density_minExponent : ℝ
  xi_bulk_curvature_depth_span_zero_density_maxExponent : ℝ

/-- Indicator width of a real exponential-polynomial segment. -/
def xi_bulk_curvature_depth_span_zero_density_indicator_width (minExponent maxExponent : ℝ) :
    ℝ :=
  maxExponent - minExponent

/-- Cartwright-style zero density attached to a real indicator width. -/
def xi_bulk_curvature_depth_span_zero_density_cartwright_zero_density
    (indicatorWidth : ℝ) : ℝ :=
  indicatorWidth / Real.pi

namespace xi_bulk_curvature_depth_span_zero_density_data

/-- Depth span of the packaged exponential-polynomial endpoints. -/
def depthSpan (D : xi_bulk_curvature_depth_span_zero_density_data) : ℝ :=
  xi_bulk_curvature_depth_span_zero_density_indicator_width
    D.xi_bulk_curvature_depth_span_zero_density_minExponent
    D.xi_bulk_curvature_depth_span_zero_density_maxExponent

/-- Zero density delivered by the Cartwright indicator-width abstraction. -/
def zeroDensity (D : xi_bulk_curvature_depth_span_zero_density_data) : ℝ :=
  xi_bulk_curvature_depth_span_zero_density_cartwright_zero_density D.depthSpan

end xi_bulk_curvature_depth_span_zero_density_data

/-- Paper label: `prop:xi-bulk-curvature-depth-span-zero-density`. -/
theorem paper_xi_bulk_curvature_depth_span_zero_density
    (D : xi_bulk_curvature_depth_span_zero_density_data) :
    D.zeroDensity = D.depthSpan / Real.pi := by
  rfl

end

end Omega.Zeta
