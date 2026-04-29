import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-window6-dimension-sieve-finite`. A conductor threshold at `660` for
the tail semigroup gives reachability for every shifted dimension at least `672`, and therefore
all unreachable dimensions are bounded by `671`. -/
theorem paper_xi_window6_dimension_sieve_finite
    (Dreach : ℕ -> Prop) (hreach : ∀ n : ℕ, 660 <= n -> Dreach (12 + n)) :
    (∀ D : ℕ, 672 <= D -> Dreach D) /\ (∀ D : ℕ, Not (Dreach D) -> D <= 671) := by
  constructor
  · intro D hD
    have hn : 660 <= D - 12 := by omega
    have hsum : 12 + (D - 12) = D := by omega
    simpa [hsum] using hreach (D - 12) hn
  · intro D hnot
    by_contra hle
    have hD : 672 <= D := by omega
    have hn : 660 <= D - 12 := by omega
    have hsum : 12 + (D - 12) = D := by omega
    exact hnot (by simpa [hsum] using hreach (D - 12) hn)

end Omega.Zeta
