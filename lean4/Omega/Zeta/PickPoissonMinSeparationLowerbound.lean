import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-pick-poisson-min-separation-lowerbound`.
Combining the determinant lower bound for `lambdaMin` with the `2 × 2` upper bound
`lambdaMin ≤ pMax * rhoMin^2` yields the separation lower bound, and comparing
`lambdaMax` against `pMax` gives the condition-number estimate. -/
theorem paper_xi_pick_poisson_min_separation_lowerbound
    (κ : Nat) (detP pSigma pMax rhoMin lambdaMax lambdaMin : Real) (hdet : 0 < detP)
    (hpSigma : 0 < pSigma) (hpMax : 0 < pMax)
    (hlambdaMin_lower : detP / pSigma ^ (κ - 1) ≤ lambdaMin)
    (hlambdaMin_upper : lambdaMin ≤ pMax * rhoMin ^ 2)
    (hlambdaMax_lower : pMax ≤ lambdaMax) :
    rhoMin ^ 2 ≥ detP / (pMax * pSigma ^ (κ - 1)) ∧
      lambdaMax / lambdaMin ≥ 1 / rhoMin ^ 2 := by
  have hpSigma_pow : 0 < pSigma ^ (κ - 1) := by positivity
  have hprod_pos : 0 < pMax * pSigma ^ (κ - 1) := by positivity
  have hlower : detP / pSigma ^ (κ - 1) ≤ pMax * rhoMin ^ 2 :=
    le_trans hlambdaMin_lower hlambdaMin_upper
  have hlower' : detP ≤ (pMax * rhoMin ^ 2) * pSigma ^ (κ - 1) := by
    exact (div_le_iff₀ hpSigma_pow).1 hlower
  have hsep : detP / (pMax * pSigma ^ (κ - 1)) ≤ rhoMin ^ 2 := by
    refine (div_le_iff₀ hprod_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlower'
  have hlambdaMin_pos : 0 < lambdaMin := by
    have : 0 < detP / pSigma ^ (κ - 1) := by positivity
    exact lt_of_lt_of_le this hlambdaMin_lower
  have hrho_sq_pos : 0 < rhoMin ^ 2 := by
    have hmul_pos : 0 < pMax * rhoMin ^ 2 := lt_of_lt_of_le hlambdaMin_pos hlambdaMin_upper
    nlinarith [hmul_pos, hpMax]
  have hrecip : (1 : Real) / rhoMin ^ 2 ≤ pMax / lambdaMin := by
    refine (div_le_div_iff₀ hrho_sq_pos hlambdaMin_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlambdaMin_upper
  have hmax : pMax / lambdaMin ≤ lambdaMax / lambdaMin := by
    exact div_le_div_of_nonneg_right hlambdaMax_lower (le_of_lt hlambdaMin_pos)
  exact ⟨hsep, le_trans hrecip hmax⟩

end Omega.Zeta
