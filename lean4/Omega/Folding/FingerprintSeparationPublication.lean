import Mathlib.Data.Set.Basic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for fingerprint separation on equi-valued raw blocks in
    `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt`.
    cor:fingerprint-separation -/
theorem paper_resolution_folding_fingerprint_separation
    {RawBlock ResidueVec Index : Type}
    (residueCode : RawBlock → ResidueVec)
    (fiber : Index → Set RawBlock)
    (hInj : Function.Injective residueCode) :
    ∀ N, Set.InjOn residueCode (fiber N) := by
  intro N ω hω ω' hω' hEq
  exact hInj hEq

end Omega.Folding
