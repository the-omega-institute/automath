import Mathlib.Tactic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace Omega.Zeta

open Filter

/-- Paper label: `cor:xi-poisson-cauchy-kl-moment-locking`.
If the fourth-order Poisson--Cauchy KL asymptotic has leading constant `Δ₂² / 8`, then an
`o(t⁻⁴)` decay forces the second-moment gap `Δ₂` to vanish. -/
theorem paper_xi_poisson_cauchy_kl_moment_locking
    (Δ₂ : ℝ) (Dkl : ℝ → ℝ)
    (hFourthOrder : Tendsto (fun t : ℝ => t ^ 4 * Dkl t) atTop (nhds (Δ₂ ^ 2 / 8)))
    (hDecay : Tendsto (fun t : ℝ => t ^ 4 * Dkl t) atTop (nhds 0)) :
    Δ₂ = 0 := by
  have hlimit : Δ₂ ^ 2 / 8 = 0 := tendsto_nhds_unique hFourthOrder hDecay
  nlinarith

end Omega.Zeta
