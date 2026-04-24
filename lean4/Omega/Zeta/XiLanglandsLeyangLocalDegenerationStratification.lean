import Mathlib.Tactic
import Omega.Zeta.P7ChebotarevSplittingDensity
import Omega.Zeta.XiTerminalZmLeyangMonodromyS4
import Omega.Zeta.XiTerminalZmS4LanglandsFactorTorusRankConductorTable

namespace Omega.Zeta

open Polynomial

/-- Paper label: `thm:xi-langlands-leyang-local-degeneration-stratification`.
This wrapper packages the already formalized `p₇` sign-channel local law, the semistable
Langlands-factor conductor table, the Lee--Yang phase-resonance parity package, and the audited
dual-root stability statement into a single local-degeneration stratification theorem. -/
theorem paper_xi_langlands_leyang_local_degeneration_stratification :
    (∀ u : ℂ,
      (∀ τ : P7S5CycleType,
        IsRoot (p7SignLocalEulerFactor τ) (p7SignEigenvalue τ) ∧ ‖p7SignEigenvalue τ‖ = 1) ∧
        p7SignLimitMeasureMass 1 = 1 / 2 ∧
        p7SignLimitMeasureMass (-1) = 1 / 2 ∧
        (∀ z : ℂ, z ≠ 1 → z ≠ -1 → p7SignLimitMeasureMass z = 0) ∧
        p7SignLogPotential u = p7SignFreeEnergy u) ∧
      (xiTerminalZmS4LanglandsTorusRanks .one = (1, 1, 1, 2) ∧
        xiTerminalZmS4LanglandsTorusRanks .two = (0, 0, 1, 1) ∧
        xiTerminalZmS4LanglandsTorusRanks .three = (1, 0, 0, 1) ∧
        xi_terminal_zm_s4_langlands_factor_torus_rank_conductor_table_conductor_exponents .one =
          (1, 1, 1, 2) ∧
        xi_terminal_zm_s4_langlands_factor_torus_rank_conductor_table_conductor_exponents .two =
          (0, 0, 1, 1) ∧
        xi_terminal_zm_s4_langlands_factor_torus_rank_conductor_table_conductor_exponents .three =
          (1, 0, 0, 1) ∧
        xiTerminalZmS4PrymDeltaTorusRank .one = 6 ∧
        xiTerminalZmS4PrymDeltaTorusRank .two = 4 ∧
        xiTerminalZmS4PrymDeltaTorusRank .three = 2 ∧
        xiTerminalZmS4PrymTauTorusRank .one = 7 ∧
        xiTerminalZmS4PrymTauTorusRank .two = 3 ∧
        xiTerminalZmS4PrymTauTorusRank .three = 3) ∧
      xiLeyangGeometricMonodromyGroup = ⊤ ∧
      xiLeyangFunctionFieldGaloisGroup = ⊤ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    exact paper_xi_p7_chebotarev_leyang_circularity_and_limit_law u
  · exact paper_xi_terminal_zm_s4_langlands_factor_torus_rank_conductor_table
  · exact paper_xi_terminal_zm_leyang_monodromy_s4.1
  · exact paper_xi_terminal_zm_leyang_monodromy_s4.2

end Omega.Zeta
