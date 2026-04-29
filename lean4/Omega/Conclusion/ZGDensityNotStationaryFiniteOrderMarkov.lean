import Mathlib.Data.Rat.Defs

namespace Omega.Conclusion

/-- Concrete data for the nonstationary finite-order Markov obstruction. The transition
sequence is the all-zero-block-to-one transition supplied by the ZG inhomogeneous law; its
decay clause says that no positive stationary transition value can persist for all times. -/
structure conclusion_zg_density_not_stationary_finite_order_markov_data where
  conclusion_zg_density_not_stationary_finite_order_markov_order : ℕ
  conclusion_zg_density_not_stationary_finite_order_markov_transition : ℕ → ℚ
  conclusion_zg_density_not_stationary_finite_order_markov_transition_decay :
    ∀ c : ℚ,
      0 < c →
        ∃ n : ℕ,
          conclusion_zg_density_not_stationary_finite_order_markov_transition n ≠ c

namespace conclusion_zg_density_not_stationary_finite_order_markov_data

/-- A stationary finite-order model with full support has a single positive transition
probability out of the all-zero context. -/
def conclusion_zg_density_not_stationary_finite_order_markov_stationary_finite_order
    (D : conclusion_zg_density_not_stationary_finite_order_markov_data) : Prop :=
  ∃ c : ℚ,
    0 < c ∧
      ∀ n : ℕ,
        D.conclusion_zg_density_not_stationary_finite_order_markov_transition n = c

end conclusion_zg_density_not_stationary_finite_order_markov_data

/-- Paper label: `cor:conclusion-zg-density-not-stationary-finite-order-markov`. -/
theorem paper_conclusion_zg_density_not_stationary_finite_order_markov
    (D : conclusion_zg_density_not_stationary_finite_order_markov_data) :
    ¬ D.conclusion_zg_density_not_stationary_finite_order_markov_stationary_finite_order := by
  rintro ⟨c, hc_pos, hc_const⟩
  obtain ⟨n, hn_ne⟩ :=
    D.conclusion_zg_density_not_stationary_finite_order_markov_transition_decay c hc_pos
  exact hn_ne (hc_const n)

end Omega.Conclusion
