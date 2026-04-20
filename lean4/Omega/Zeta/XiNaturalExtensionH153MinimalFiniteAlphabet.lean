import Omega.Zeta.LayeredPrimesliceLocalAlphabetFibermax

namespace Omega.Zeta

/-- Paper label: `thm:xi-natural-extension-h153-minimal-finite-alphabet`. -/
theorem paper_xi_natural_extension_h153_minimal_finite_alphabet
    {X Y A : Type*} [Fintype X] [Fintype A]
    (pi : X → Y) (M : Nat)
    (hmax : ∀ y, Nat.card (LayerFiber pi y) ≤ M)
    (hwit : ∃ y, Nat.card (LayerFiber pi y) = M) :
    (∃ q : X → A, FiberwiseInjective pi q) ↔ M ≤ Fintype.card A := by
  simpa using
    (paper_xi_layered_primeslice_local_alphabet_fibermax (Λ := A) (π := pi) (B := M) hmax hwit)

end Omega.Zeta
