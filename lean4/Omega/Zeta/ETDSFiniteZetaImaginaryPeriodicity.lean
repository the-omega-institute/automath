import Omega.Zeta.DynZeta

namespace Omega.Zeta

/-- A `2π i`-periodic finite-kernel side cannot agree everywhere with a comparison function that
fails the same periodicity at one explicit point.
    thm:zeta-syntax-finite-zeta-imaginary-periodicity -/
theorem paper_zeta_syntax_finite_zeta_imaginary_periodicity (F zeta : Complex → Complex) :
    (∀ s, F (s + (2 * Real.pi) * Complex.I) = F s) →
      (∃ s, zeta (s + (2 * Real.pi) * Complex.I) ≠ zeta s) →
      ¬ ∀ s, F s = zeta s := by
  intro hF hzeta hEq
  rcases hzeta with ⟨s, hs⟩
  apply hs
  calc
    zeta (s + (2 * Real.pi) * Complex.I) = F (s + (2 * Real.pi) * Complex.I) := by
      symm
      exact hEq _
    _ = F s := hF s
    _ = zeta s := hEq _

end Omega.Zeta
