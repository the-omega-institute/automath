import Mathlib.Tactic
import Omega.Folding.Entropy

namespace Omega.GU

open Filter Topology
open scoped goldenRatio

/-- Protocol-level entropy-time sequence for the golden-mean baseline. -/
noncomputable def entropyTime (t : ℕ) : ℝ :=
  Real.log (Nat.fib (t + 2) : ℝ)

/-- Paper-facing asymptotic: the entropy accumulated over `t` time units has limiting density
`log φ`. `prop:time-unit-logphi-protocol` -/
theorem paper_time_unit_logphi_protocol :
    Tendsto (fun t => entropyTime t / (t : ℝ)) atTop (𝓝 (Real.log φ)) := by
  simpa [entropyTime] using Omega.Entropy.topological_entropy_eq_log_phi

/-- The terminal entropy-density correction is governed by `log φ`, and the reciprocal form using
`log (φ⁻¹)` simplifies to the same constant.
    cor:terminal-tau-corr-logphi -/
theorem paper_terminal_tau_corr_logphi :
    Tendsto (fun t => entropyTime t / (t : ℝ)) atTop (𝓝 (Real.log Real.goldenRatio)) ∧
      1 / (-Real.log (Real.goldenRatio⁻¹ : ℝ)) = 1 / Real.log Real.goldenRatio := by
  refine ⟨?_, ?_⟩
  · simpa using paper_time_unit_logphi_protocol
  · rw [Real.log_inv]
    simp

end Omega.GU
