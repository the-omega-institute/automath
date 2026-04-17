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

end Omega.GU
