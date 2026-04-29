import Omega.Zeta.BdryFreeInvolutionOddFiberObstructionMinCover

namespace Omega.Zeta

/-- Paper label: `cor:xi-bdry-uplift-three-layer-needs-one-bit`. -/
theorem paper_xi_bdry_uplift_three_layer_needs_one_bit {X Y : Type} [Fintype X] [Fintype Y]
    (f : Y → X) (x : X) (hodd : Odd (Fintype.card {y // f y = x})) :
    (∀ σ : Y → Y, Function.Involutive σ → (∀ y, σ y ≠ y) →
      (∀ y, f (σ y) = f y) → False) := by
  intro σ hσ hfree hcompat
  have heven :
      Even (Fintype.card {y // f y = x}) :=
    paper_xi_bdry_free_involution_odd_fiber_obstruction_min_cover f σ hσ hfree hcompat x
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end Omega.Zeta
