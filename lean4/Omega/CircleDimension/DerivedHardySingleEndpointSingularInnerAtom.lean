import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper label: `thm:derived-hardy-single-endpoint-singular-inner-atom`. -/
theorem paper_derived_hardy_single_endpoint_singular_inner_atom
    (zeta0 : ℂ) (analyticAwayFromEndpoint singularSupportAtEndpoint singularInnerAtomAt : Prop)
    (hAnalytic : analyticAwayFromEndpoint)
    (hSupport : analyticAwayFromEndpoint → singularSupportAtEndpoint)
    (hAtom : singularSupportAtEndpoint → singularInnerAtomAt) :
    analyticAwayFromEndpoint ∧ singularSupportAtEndpoint ∧ singularInnerAtomAt := by
  let _ := zeta0
  exact ⟨hAnalytic, hSupport hAnalytic, hAtom (hSupport hAnalytic)⟩

end Omega.CircleDimension
