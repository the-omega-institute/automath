import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zn-window6-pushforward-algebra-full-matrixization`.
Off-diagonal matrix units are already in the Lie subspace inside the algebra, and diagonal
matrix units are products of opposite off-diagonal units through a second index. -/
theorem paper_xi_time_part9zn_window6_pushforward_algebra_full_matrixization {V End : Type*}
    [Fintype V] [DecidableEq V] (A sl : Set End) (mul : End → End → End)
    (E : V → V → End) (hsl_sub : sl ⊆ A) (hoffdiag_sl : ∀ u v, u ≠ v → E u v ∈ sl)
    (hdiag_mul : ∀ u v, u ≠ v → mul (E u v) (E v u) = E u u)
    (hmul : ∀ x ∈ A, ∀ y ∈ A, mul x y ∈ A) (hne : ∀ u : V, ∃ v : V, v ≠ u) :
    ∀ u v, E u v ∈ A := by
  intro u v
  by_cases huv : u = v
  · subst v
    rcases hne u with ⟨w, hwu⟩
    have huw : u ≠ w := fun huw => hwu huw.symm
    have huwA : E u w ∈ A := hsl_sub (hoffdiag_sl u w huw)
    have hwuA : E w u ∈ A := hsl_sub (hoffdiag_sl w u hwu)
    simpa [hdiag_mul u w huw] using hmul (E u w) huwA (E w u) hwuA
  · exact hsl_sub (hoffdiag_sl u v huv)

end Omega.Zeta
