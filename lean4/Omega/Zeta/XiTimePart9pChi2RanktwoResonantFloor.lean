import Mathlib.Tactic
import Omega.Zeta.XiFoldFibonacciCollisionGapPositiveFloor
import Omega.Zeta.XiFoldbinKappaKlCollisionIdentityChain

namespace Omega.Zeta

open Omega.Folding

noncomputable section

/-- The explicit `χ² + 1` collision quantity appearing in the rank-two resonance package. -/
def xi_time_part9p_chi2_ranktwo_resonant_floor_collision_mass (m : ℕ) : ℝ :=
  (Fintype.card (Omega.X m) : ℝ) * (Omega.Folding.foldBinCollisionMass m : ℚ)

/-- The positive resonant two-frequency floor carried by the Fibonacci witness. -/
def xi_time_part9p_chi2_ranktwo_resonant_floor_floor (Cphi : ℝ) : ℝ :=
  xiFoldFibonacciNormalizedGap Cphi - xiFoldFibonacciMeanFiber Cphi

/-- Paper-facing package for the rank-two resonant floor: the nontrivial `χ²` term rewrites as the
uniform-baseline collision mass minus `1`, and the Fibonacci two-frequency witness contributes a
strictly positive floor. -/
def xi_time_part9p_chi2_ranktwo_resonant_floor_statement : Prop :=
  ∀ m : ℕ, ∀ Cphi : ℝ,
    (((Omega.Folding.foldBinChi2Col m : ℚ) : ℝ) + 1 =
      xi_time_part9p_chi2_ranktwo_resonant_floor_collision_mass m) ∧
    0 < xi_time_part9p_chi2_ranktwo_resonant_floor_floor Cphi

theorem paper_xi_time_part9p_chi2_ranktwo_resonant_floor :
    xi_time_part9p_chi2_ranktwo_resonant_floor_statement := by
  intro m Cphi
  have hchain := paper_xi_foldbin_kappa_kl_collision_identity_chain 0 (by positivity) m
  refine ⟨?_, ?_⟩
  · simpa [xi_time_part9p_chi2_ranktwo_resonant_floor_collision_mass] using hchain.2.2.2
  · simpa [XiFoldFibonacciCollisionGapPositiveFloor,
      xi_time_part9p_chi2_ranktwo_resonant_floor_floor] using
      paper_xi_fold_fibonacci_collision_gap_positive_floor Cphi

end

end Omega.Zeta
