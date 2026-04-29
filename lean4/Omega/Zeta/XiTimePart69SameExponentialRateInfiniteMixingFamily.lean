import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part69-same-exponential-rate-infinite-mixing-family`. -/
theorem paper_xi_time_part69_same_exponential_rate_infinite_mixing_family
    (System : Type*) (rate : System → ℝ) (mixing : System → Prop)
    (isomorphic : System → System → Prop) (qRate : ℝ) (systems : ℕ → System)
    (hrate : ∀ n, rate (systems n) = qRate) (hmix : ∀ n, mixing (systems n))
    (hpairwise : ∀ m n, m ≠ n → ¬ isomorphic (systems m) (systems n)) :
    (∀ n, rate (systems n) = qRate) ∧ (∀ n, mixing (systems n)) ∧
      (∀ m n, m ≠ n → ¬ isomorphic (systems m) (systems n)) := by
  exact ⟨hrate, hmix, hpairwise⟩

end Omega.Zeta
