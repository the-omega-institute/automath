import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-layered-prime-register-sharp-natural-extension`. -/
theorem paper_xi_layered_prime_register_sharp_natural_extension (k minSlices : ℕ)
    (HasBranch ActiveSlice : Fin k → Prop)
    (ExactExternalization ConstructedOnePerLayer : Prop)
    (force_active : ExactExternalization → ∀ j, HasBranch j → ActiveSlice j)
    (all_branches : ∀ j, HasBranch j)
    (lower : (∀ j, ActiveSlice j) → k ≤ minSlices)
    (upper : ConstructedOnePerLayer → minSlices ≤ k) :
    ExactExternalization → ConstructedOnePerLayer → minSlices = k := by
  intro hExternal hConstructed
  refine le_antisymm (upper hConstructed) (lower ?_)
  intro j
  exact force_active hExternal j (all_branches j)

end Omega.Zeta
