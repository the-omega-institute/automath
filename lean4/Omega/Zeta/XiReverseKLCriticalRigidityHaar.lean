import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Fourier certificate data for `cor:xi-reversekl-critical-rigidity-haar`. -/
structure xi_reversekl_critical_rigidity_haar_data where
  fourierCoeff : ℕ → ℝ
  scale : ℕ → ℝ
  scale_pos : ∀ step : ℕ, 0 < scale step
  finite_fourier_lower_bound_certificate :
    ∀ freq step : ℕ, 0 < freq → scale step * fourierCoeff freq ^ 2 ≤ 0

def xi_reversekl_critical_rigidity_haar_statement
    (D : xi_reversekl_critical_rigidity_haar_data) : Prop :=
  ∀ freq : ℕ, 0 < freq → D.fourierCoeff freq = 0

/-- Paper label: `cor:xi-reversekl-critical-rigidity-haar`. -/
theorem paper_xi_reversekl_critical_rigidity_haar
    (D : xi_reversekl_critical_rigidity_haar_data) :
    xi_reversekl_critical_rigidity_haar_statement D := by
  intro freq hfreq
  have hscale : 0 < D.scale 0 := D.scale_pos 0
  have hcert : D.scale 0 * D.fourierCoeff freq ^ 2 ≤ 0 :=
    D.finite_fourier_lower_bound_certificate freq 0 hfreq
  have hprod_nonneg : 0 ≤ D.scale 0 * D.fourierCoeff freq ^ 2 :=
    mul_nonneg (le_of_lt hscale) (sq_nonneg (D.fourierCoeff freq))
  have hprod_zero : D.scale 0 * D.fourierCoeff freq ^ 2 = 0 :=
    le_antisymm hcert hprod_nonneg
  have hsquare_zero : D.fourierCoeff freq ^ 2 = 0 :=
    (mul_eq_zero.mp hprod_zero).resolve_left (ne_of_gt hscale)
  nlinarith [sq_nonneg (D.fourierCoeff freq)]

end Omega.Zeta
