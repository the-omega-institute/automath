import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62ae-anomaly-infinite-rank-dichotomy`. -/
theorem paper_xi_time_part62ae_anomaly_infinite_rank_dichotomy {Prime : Type*}
    (S : ℕ → Finset Prime) (rank : ℕ → ℕ) (StrictHom Anomaly : Prop)
    (hCofinalUnbounded : ∀ R : ℕ, ∃ n, R < (S n).card)
    (hFaithfulRank : StrictHom → ∀ n, (S n).card ≤ rank n) :
    (¬ ∃ R : ℕ, ∀ n, rank n ≤ R) ∨ Anomaly ∨ ¬ StrictHom := by
  by_cases hStrict : StrictHom
  · left
    rintro ⟨R, hBound⟩
    rcases hCofinalUnbounded R with ⟨n, hn⟩
    exact Nat.not_lt_of_ge (le_trans (hFaithfulRank hStrict n) (hBound n)) hn
  · exact Or.inr (Or.inr hStrict)

end Omega.Zeta
