import Mathlib.Data.Set.Basic

namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Paper-facing soundness wrapper: once the global derivation system is sound for the
    local forcing semantics, every derivable conclusion is forced at any state satisfying
    the hypotheses.
    prop:observer-indexed-global-layer-logic-only -/
theorem paper_recursive_addressing_observer_indexed_global_layer_logic_only
    {State Formula : Type}
    (Forces : State → Formula → Prop)
    (Derives : Set Formula → Formula → Prop)
    (hsound : ∀ {Gamma phi p}, Derives Gamma phi →
      (∀ psi ∈ Gamma, Forces p psi) → Forces p phi)
    {Gamma : Set Formula} {phi : Formula} {p : State}
    (hderiv : Derives Gamma phi)
    (hGamma : ∀ psi ∈ Gamma, Forces p psi) : Forces p phi := by
  exact hsound hderiv hGamma

/-- Paper label: `prop:observer-indexed-global-layer-logic-only`. -/
theorem paper_observer_indexed_global_layer_logic_only
    {State Formula : Type}
    (Forces : State → Formula → Prop)
    (Derives : Set Formula → Formula → Prop)
    (hsound : ∀ {Gamma phi p}, Derives Gamma phi →
      (∀ psi ∈ Gamma, Forces p psi) → Forces p phi)
    {Gamma : Set Formula} {phi : Formula} {p : State}
    (hderiv : Derives Gamma phi)
    (hGamma : ∀ psi ∈ Gamma, Forces p psi) : Forces p phi := by
  exact hsound hderiv hGamma

end Omega.RecursiveAddressing
