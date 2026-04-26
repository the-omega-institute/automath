import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite data for the `v₂` odd-fiber upper-bound argument. Odd fibers are included in
the low-valuation event; the latter is bounded by a uniform block estimate, and the block estimate
is bounded by an exponential rate strictly below `phi`. -/
structure xi_fold_odd_fiber_exponential_upper_bound_from_v2_data where
  m : ℕ
  phi : ℝ
  rate : ℝ
  uniformProbabilityBound : ℝ
  blocks : Finset ℕ
  oddFibers : Finset ℕ
  lowValuationEvents : Finset ℕ
  oddFiberLowValuation : oddFibers ⊆ lowValuationEvents
  lowValuationUniformBound :
    (lowValuationEvents.card : ℝ) ≤ (blocks.card : ℝ) * uniformProbabilityBound
  fibonacciGrowthBound : (blocks.card : ℝ) * uniformProbabilityBound ≤ rate ^ m
  rate_lt_phi : rate < phi

namespace xi_fold_odd_fiber_exponential_upper_bound_from_v2_data

/-- The concrete exponential upper bound for the number of odd fibers, with rate strictly below
the golden-ratio scale `phi`. -/
def oddFibersExponentiallyBounded
    (D : xi_fold_odd_fiber_exponential_upper_bound_from_v2_data) : Prop :=
  (D.oddFibers.card : ℝ) ≤ D.rate ^ D.m ∧ D.rate < D.phi

end xi_fold_odd_fiber_exponential_upper_bound_from_v2_data

/-- Paper label: `thm:xi-fold-odd-fiber-exponential-upper-bound-from-v2`. -/
theorem paper_xi_fold_odd_fiber_exponential_upper_bound_from_v2
    (D : xi_fold_odd_fiber_exponential_upper_bound_from_v2_data) :
    D.oddFibersExponentiallyBounded := by
  refine ⟨?_, D.rate_lt_phi⟩
  have hCardNat : D.oddFibers.card ≤ D.lowValuationEvents.card :=
    Finset.card_le_card D.oddFiberLowValuation
  have hCardReal : (D.oddFibers.card : ℝ) ≤ D.lowValuationEvents.card := by
    exact_mod_cast hCardNat
  exact le_trans hCardReal (le_trans D.lowValuationUniformBound D.fibonacciGrowthBound)

end Omega.Zeta
