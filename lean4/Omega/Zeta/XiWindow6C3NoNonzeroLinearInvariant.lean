import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic
import Omega.Zeta.XiWindow6C3QuadraticEnergyEquipartition

namespace Omega.Zeta

/-- Paper label: `cor:xi-window6-c3-no-nonzero-linear-invariant`. -/
theorem paper_xi_window6_c3_no_nonzero_linear_invariant :
    (xiWindow6LongRoots ++ xiWindow6ShortRoots).sum = ((0 : ℤ), 0, 0) := by
  simp [xiWindow6LongRoots, xiWindow6ShortRoots]

/-- Any additive linear functional on the `C₃` root packet has vanishing total sum. -/
theorem xiWindow6_linear_functional_vanish (ℓ : XiWindow6Root →+ ℤ) :
    ((xiWindow6LongRoots ++ xiWindow6ShortRoots).map ℓ).sum = 0 := by
  calc
    ((xiWindow6LongRoots ++ xiWindow6ShortRoots).map ℓ).sum =
        ℓ ((xiWindow6LongRoots ++ xiWindow6ShortRoots).sum) := by
          symm
          exact map_list_sum ℓ (xiWindow6LongRoots ++ xiWindow6ShortRoots)
    _ = ℓ ((0 : ℤ), 0, 0) := by
          simpa using congrArg ℓ paper_xi_window6_c3_no_nonzero_linear_invariant
    _ = 0 := by
          rw [show (((0 : ℤ), 0, 0) : XiWindow6Root) = 0 by rfl, ℓ.map_zero]

end Omega.Zeta
