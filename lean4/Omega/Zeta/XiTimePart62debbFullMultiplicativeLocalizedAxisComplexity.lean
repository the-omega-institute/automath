import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart62debbFiniteLocalizationAxesNoFullMultiplicativeHost

namespace Omega.Zeta

/-- Paper label:
`cor:xi-time-part62debb-full-multiplicative-localized-axis-complexity`. Every finite localized
axis budget misses the next prime generator, while the countable free commutative monoid is its
own explicit countable witness. -/
theorem paper_xi_time_part62debb_full_multiplicative_localized_axis_complexity :
    (∀ a b : ℕ, ¬ Omega.Zeta.xiLocalizedAxisThreshold (a + b + 1) a b) ∧
      Nonempty ((ℕ →₀ ℕ) ≃ (ℕ →₀ ℕ)) := by
  exact ⟨paper_xi_time_part62debb_finite_localization_axes_no_full_multiplicative_host,
    ⟨Equiv.refl _⟩⟩

end Omega.Zeta
