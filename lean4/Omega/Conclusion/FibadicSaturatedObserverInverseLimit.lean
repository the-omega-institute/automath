import Mathlib.Data.ZMod.Basic
import Omega.Conclusion.FibadicProfiniteCollapseToZhat

namespace Omega.Conclusion

open Omega.Zeta

/-- Paper label: `thm:conclusion-fibadic-saturated-observer-inverse-limit`.
The cofinal Fibonacci subsystem already recovers the fibadic inverse limit, and adjoining a
constant observer factor `(ℤ/2ℤ)^β` simply products the same equivalence with the identity. -/
theorem paper_conclusion_fibadic_saturated_observer_inverse_limit (beta : ℕ) :
    ConclusionFibadicProfiniteCollapseToZhat ∧
      Nonempty (((Fin beta → ZMod 2) × FibadicAddressInverseLimit) ≃
        ((Fin beta → ZMod 2) × Zhat)) := by
  rcases paper_conclusion_fibadic_profinite_collapse_to_zhat with ⟨hcofinal, hcompletion, haddr⟩
  rcases haddr with ⟨e⟩
  refine ⟨⟨hcofinal, hcompletion, ⟨e⟩⟩, ?_⟩
  exact ⟨Equiv.prodCongr (Equiv.refl _) e.toEquiv⟩

end Omega.Conclusion
