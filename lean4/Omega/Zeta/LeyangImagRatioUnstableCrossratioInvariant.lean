import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-leyang-imag-ratio-unstable-crossratio-invariant`. -/
theorem paper_xi_leyang_imag_ratio_unstable_crossratio_invariant {K : Type} [Field K]
    (a b c d τ : K) :
    ((a + τ - c - τ) * (b + τ - d - τ)) /
        ((a + τ - d - τ) * (b + τ - c - τ)) =
      ((a - c) * (b - d)) / ((a - d) * (b - c)) := by
  ring_nf

end Omega.Zeta
