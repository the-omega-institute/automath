import Mathlib.Tactic
import Omega.Conclusion.AffineRegisterBudget

namespace Omega.Conclusion

/-- Concrete selector-complexity data: an exact selector injects the `p^(ℓr)` kernel states into
`stateCount` states, and the Smith-normal-form coordinates identify the optimal `p^(ℓr)`-state
selector with the identity map on `Fin (p^(ℓr))`. -/
structure BoundaryExactSelectorComplexityData where
  p : ℕ
  ell : ℕ
  r : ℕ
  stateCount : ℕ
  selector : Fin (p ^ (ell * r)) → Fin stateCount
  selector_injective : Function.Injective selector

namespace BoundaryExactSelectorComplexityData

/-- The number of kernel coordinates selected in Smith normal form. -/
def kernelStateCount (D : BoundaryExactSelectorComplexityData) : ℕ :=
  D.p ^ (D.ell * D.r)

/-- Any exact selector needs at least `p^(ℓr)` states. -/
def lowerBound (D : BoundaryExactSelectorComplexityData) : Prop :=
  D.kernelStateCount ≤ D.stateCount

/-- The Smith-normal-form selector is modeled by the identity map on the kernel coordinates. -/
def smithNormalFormSelector (D : BoundaryExactSelectorComplexityData) :
    Fin D.kernelStateCount → Fin D.kernelStateCount :=
  id

/-- An explicit optimal selector exists on exactly `p^(ℓr)` states. -/
def explicitOptimalSelector (D : BoundaryExactSelectorComplexityData) : Prop :=
  ∃ f : Fin D.kernelStateCount → Fin D.kernelStateCount, Function.Injective f

end BoundaryExactSelectorComplexityData

open BoundaryExactSelectorComplexityData

/-- Use the existing cycle-rank/register-budget lower bound to force at least `p^(ℓr)` states for
any exact selector, then realize that bound by choosing the Smith-normal-form kernel coordinates.
    thm:conclusion-boundary-exact-selector-complexity -/
theorem paper_conclusion_boundary_exact_selector_complexity
    (h : BoundaryExactSelectorComplexityData) : h.lowerBound ∧ h.explicitOptimalSelector := by
  refine ⟨?_, ?_⟩
  · simpa [BoundaryExactSelectorComplexityData.lowerBound,
      BoundaryExactSelectorComplexityData.kernelStateCount] using
      registerBudget_min_card h.p (h.ell * h.r) h.stateCount ⟨h.selector, h.selector_injective⟩
  · refine ⟨h.smithNormalFormSelector, ?_⟩
    intro x y hxy
    exact hxy

end Omega.Conclusion
