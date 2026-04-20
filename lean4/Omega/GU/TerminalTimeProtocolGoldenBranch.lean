import Omega.GU.TerminalOstrowskiZeckendorfBinfold
import Omega.GU.TerminalTimeFactorMetallicUnique
import Omega.GU.TimeUnitLogphiProtocol

namespace Omega.GU

open Filter Topology
open scoped goldenRatio

/-- Paper label: `thm:terminal-time-protocol-golden-branch`. -/
theorem paper_terminal_time_protocol_golden_branch :
    Tendsto (fun t => Omega.GU.entropyTime t / (t : ℝ)) Filter.atTop
        (𝓝 (Real.log Real.goldenRatio)) ∧
      (∀ m N : Nat, Omega.Folding.OstrowskiDenominators.ostrowskiDenom (fun _ => 1) m =
        Nat.fib (m + 1)) ∧
      (∀ A : Nat, 1 ≤ A → Omega.GU.terminalTimeRotationClock 1 ≤ Omega.GU.terminalTimeRotationClock A) := by
  refine ⟨?_, ?_, Omega.GU.paper_terminal_time_factor_metallic_unique.1⟩
  · simpa [Omega.GU.entropyTime] using Omega.Entropy.topological_entropy_eq_log_phi
  · intro m _
    simpa using Omega.Folding.OstrowskiDenominators.ostrowskiDenom_const_one_eq_fib m

end Omega.GU
