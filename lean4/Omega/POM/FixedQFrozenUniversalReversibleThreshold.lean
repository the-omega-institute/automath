import Mathlib.Tactic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed

open Filter Topology

namespace Omega.POM

/-- Frozen-zone reversible-capacity threshold: if the maximal-fiber mass tends to `1` and the
code-budget ratio tends to `λ`, then the optimal success rate tends to `min (1, λ)`.
    thm:pom-fixedq-frozen-universal-reversible-threshold -/
theorem paper_pom_fixedq_frozen_universal_reversible_threshold
    (succ massOnMax ratio : Nat → Real) (lam : Real)
    (hBounds : ∀ m,
      massOnMax m * min (1 : Real) (ratio m) ≤ succ m ∧
        succ m ≤ massOnMax m * min (1 : Real) (ratio m) + (1 - massOnMax m))
    (hMass : Filter.Tendsto massOnMax Filter.atTop (𝓝 1))
    (hRatio : Filter.Tendsto ratio Filter.atTop (𝓝 lam)) :
    Filter.Tendsto succ Filter.atTop (𝓝 (min (1 : Real) lam)) := by
  have hmin : Filter.Tendsto (fun m => min (1 : Real) (ratio m)) Filter.atTop
      (𝓝 (min (1 : Real) lam)) := by
    let f : Real → Real := fun x => min (1 : Real) x
    have hf : Continuous f := continuous_const.min continuous_id
    simpa [f] using (hf.continuousAt.tendsto.comp hRatio)
  have hmain : Filter.Tendsto (fun m => massOnMax m * min (1 : Real) (ratio m)) Filter.atTop
      (𝓝 (min (1 : Real) lam)) := by
    simpa using (hMass.mul hmin)
  have hmass_err : Filter.Tendsto (fun m => 1 - massOnMax m) Filter.atTop (𝓝 0) := by
    have hsub : Filter.Tendsto (fun m => (1 : Real) - massOnMax m) Filter.atTop
        (𝓝 ((1 : Real) - 1)) := by
      exact tendsto_const_nhds.sub hMass
    simpa using hsub
  have hupper : Filter.Tendsto
      (fun m => massOnMax m * min (1 : Real) (ratio m) + (1 - massOnMax m)) Filter.atTop
      (𝓝 (min (1 : Real) lam)) := by
    simpa using (hmain.add hmass_err)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hmain hupper
    (fun m => (hBounds m).1) (fun m => (hBounds m).2)

end Omega.POM
