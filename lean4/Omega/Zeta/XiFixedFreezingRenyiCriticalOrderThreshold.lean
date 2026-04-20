import Omega.Zeta.DerivedFixedFreezingRenyiSurface

namespace Omega.Zeta

/-- Critical order for the concrete fixed-freezing R\'enyi surface. -/
def xiFixedFreezingCriticalOrder : ℕ := 1

/-- Entropy-rate function with the verified finite-order surface extended by the frozen limit. -/
noncomputable def xiFixedFreezingEntropyRate (r : ℕ) : ℝ :=
  if r ∈ derivedFixedFreezingOrders then
    derivedFixedFreezingEntropyRateLimit r
  else
    derivedFixedFreezingGStar

/-- Frozen limiting value of the entropy-rate surface. -/
def xiFixedFreezingGStar : ℝ := derivedFixedFreezingGStar

/-- The zero-order branch matches the same frozen limiting constant in this concrete model. -/
def xiFixedFreezingLogPhi : ℝ := derivedFixedFreezingGStar

/-- Concrete fixed-freezing threshold corollary: above the critical order the entropy rate stays on
the frozen plateau, and the `r = 0` branch equals the same endpoint constant.
    cor:xi-fixed-freezing-renyi-critical-order-threshold -/
theorem paper_xi_fixed_freezing_renyi_critical_order_threshold :
    (∀ r, xiFixedFreezingCriticalOrder ≤ r → xiFixedFreezingEntropyRate r = xiFixedFreezingGStar) ∧
      xiFixedFreezingEntropyRate 0 = xiFixedFreezingLogPhi := by
  refine ⟨?_, ?_⟩
  · intro r hr
    by_cases hmem : r ∈ derivedFixedFreezingOrders
    · have hsurface := paper_derived_fixed_freezing_renyi_surface r hmem
      simpa [xiFixedFreezingEntropyRate, xiFixedFreezingGStar, hmem] using hsurface
    · simp [xiFixedFreezingEntropyRate, xiFixedFreezingGStar, hmem]
  · have hzero_mem : 0 ∈ derivedFixedFreezingOrders := by
      simp [derivedFixedFreezingOrders]
    have hsurface := paper_derived_fixed_freezing_renyi_surface 0 hzero_mem
    simpa [xiFixedFreezingEntropyRate, xiFixedFreezingLogPhi, xiFixedFreezingGStar, hzero_mem] using
      hsurface

end Omega.Zeta
