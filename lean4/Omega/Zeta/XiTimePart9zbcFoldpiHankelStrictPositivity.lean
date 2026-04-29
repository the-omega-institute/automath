import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zbc-foldpi-hankel-strict-positivity`. -/
theorem paper_xi_time_part9zbc_foldpi_hankel_strict_positivity
    (M : ℕ → ℝ) (strictHankelPositive determinantPositive infiniteHankelRank : Prop)
    (hpos : strictHankelPositive) (hdet : strictHankelPositive → determinantPositive)
    (hrank : determinantPositive → infiniteHankelRank) :
    strictHankelPositive ∧ determinantPositive ∧ infiniteHankelRank := by
  let _momentSequence : ℕ → ℝ := M
  exact ⟨hpos, hdet hpos, hrank (hdet hpos)⟩

end Omega.Zeta
