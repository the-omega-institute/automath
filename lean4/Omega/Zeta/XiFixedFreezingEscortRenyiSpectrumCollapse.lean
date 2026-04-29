import Mathlib.Analysis.SpecialFunctions.Exp
import Omega.Zeta.DerivedFixedFreezingRenyiSurface

namespace Omega.Zeta

/-- Concrete order data for the fixed-freezing escort R\'enyi collapse package. -/
structure xi_fixed_freezing_escort_renyi_spectrum_collapse_data where
  order : ℕ
  horder : order ∈ derivedFixedFreezingOrders

/-- At every registered order, the concrete fixed-freezing escort R\'enyi surface already sits on
the frozen value `g_* = 0`, and the companion frozen-escort concentration package is available at
the same time. -/
def xi_fixed_freezing_escort_renyi_spectrum_collapse_statement
    (D : xi_fixed_freezing_escort_renyi_spectrum_collapse_data) : Prop :=
  derivedFixedFreezingEntropyRateLimit D.order = derivedFixedFreezingGStar ∧
    derivedFixedFreezingTvData.tvDistance = 1 - derivedFixedFreezingTvData.massOnMaxFiber ∧
    derivedFixedFreezingTvData.tvDistance ≤ Real.exp (-derivedFixedFreezingTvData.exponentialGap) ∧
    XiFixedFreezingEscortObservableData.exponentialObservableCollapse
      derivedFixedFreezingObservableData

/-- Paper label: `thm:xi-fixed-freezing-escort-renyi-spectrum-collapse`. The concrete frozen
three-state model already has a collapsed escort R\'enyi surface on the registered orders, and the
same model carries the exact frozen-escort TV identity together with bounded-observable collapse.
-/
theorem paper_xi_fixed_freezing_escort_renyi_spectrum_collapse
    (D : xi_fixed_freezing_escort_renyi_spectrum_collapse_data) :
    xi_fixed_freezing_escort_renyi_spectrum_collapse_statement D := by
  have hsurface := paper_derived_fixed_freezing_renyi_surface D.order D.horder
  have hfreeze := paper_derived_fixed_freezing_microcanonical_tv
  exact ⟨hsurface, hfreeze.1, hfreeze.2.1, hfreeze.2.2⟩

end Omega.Zeta
