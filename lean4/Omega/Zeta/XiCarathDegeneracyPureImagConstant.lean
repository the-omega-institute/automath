import Mathlib.Analysis.Complex.OpenMapping

namespace Omega.Zeta

/-- If a holomorphic Carathéodory degeneracy has vanishing real part on the unit disk, then it is
constant and purely imaginary.

Paper label: `prop:xi-carath-degeneracy-pure-imag-constant`. -/
theorem paper_xi_carath_degeneracy_pure_imag_constant (C : ℂ → ℂ)
    (hC : DifferentiableOn ℂ C (Metric.ball (0 : ℂ) 1))
    (hRe : ∀ w ∈ Metric.ball (0 : ℂ) 1, (C w).re = 0) :
    ∃ c : ℝ, ∀ w ∈ Metric.ball (0 : ℂ) 1, C w = c * Complex.I := by
  have hconn : IsConnected (Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).isConnected ⟨0, by simp⟩
  obtain ⟨c, hc⟩ :=
    (hC.analyticOnNhd Metric.isOpen_ball).eq_re_add_const_mul_I_of_re_eq_const hRe
      Metric.isOpen_ball hconn
  refine ⟨c, ?_⟩
  intro w hw
  simpa using hc w hw

end Omega.Zeta
