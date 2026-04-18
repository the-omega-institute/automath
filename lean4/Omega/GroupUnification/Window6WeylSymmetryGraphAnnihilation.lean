import Mathlib

namespace Omega.GroupUnification

/-- Paper-facing wrapper for the window-6 graph-rigidity input: any adjacency-preserving
permutation is trivial once the underlying graph has trivial automorphism group.
    thm:window6-weyl-symmetry-graph-annihilation -/
theorem paper_window6_weyl_symmetry_graph_annihilation {X : Type} (Adj : X → X → Prop)
    (σ : Equiv.Perm X)
    (hRigid : ∀ τ : Equiv.Perm X,
      (∀ a b, Adj a b ↔ Adj (τ a) (τ b)) → τ = Equiv.refl X)
    (hAdj : ∀ a b, Adj a b ↔ Adj (σ a) (σ b)) : σ = Equiv.refl X := by
  exact hRigid σ hAdj

end Omega.GroupUnification
