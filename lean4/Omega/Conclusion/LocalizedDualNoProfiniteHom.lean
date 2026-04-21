import Mathlib.Tactic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Connected.TotallyDisconnected
import Omega.Conclusion.ConnectedToDiscreteConstant

namespace Omega.Conclusion

open Set Topology

/-- Concrete connected model for the localized dual / localized solenoid. -/
abbrev LocalizedDualConnectedModel := ℝ

/-- Continuous homomorphisms out of the connected localized-dual model are trivial on totally
disconnected targets; in particular every finite continuous quotient has singleton range. -/
def LocalizedDualNoProfiniteHomStatement : Prop :=
  (∀ {P : Type*} [AddCommGroup P] [TopologicalSpace P] [TotallyDisconnectedSpace P]
      (f : LocalizedDualConnectedModel →+ P), Continuous f → ∀ x, f x = 0) ∧
    (∀ {H : Type*} [AddCommGroup H] [Fintype H] [TopologicalSpace H] [DiscreteTopology H]
      (f : LocalizedDualConnectedModel →+ H), Continuous f → Set.range f = ({0} : Set H))

/-- Paper label: `thm:conclusion-localized-dual-no-profinite-hom`. The connected localized-dual
source admits no nontrivial continuous additive homomorphism into a totally disconnected target,
and the finite-quotient case collapses to the singleton subgroup `{0}`. -/
theorem paper_conclusion_localized_dual_no_profinite_hom :
    LocalizedDualNoProfiniteHomStatement := by
  refine ⟨?_, ?_⟩
  · intro P _ _ _ f hf x
    have hconst : f x = f 0 :=
      TotallyDisconnectedSpace.eq_of_continuous (f : LocalizedDualConnectedModel → P) hf x 0
    simpa [hconst] using f.map_zero
  · intro H _ _ _ _ f hf
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hzero :=
        Omega.Conclusion.ConnectedToDiscreteConstant.continuous_hom_connected_to_discrete_zero f hf x
      simpa [hzero]
    · intro hy
      have hzero0 :
          f 0 = 0 :=
        Omega.Conclusion.ConnectedToDiscreteConstant.continuous_hom_connected_to_discrete_zero
          f hf 0
      exact ⟨0, hzero0.trans hy.symm⟩

end Omega.Conclusion
