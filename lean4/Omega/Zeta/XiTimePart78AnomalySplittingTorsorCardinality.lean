import Mathlib.Tactic
import Mathlib.Data.Fintype.Pi

namespace Omega.Zeta.XiTimePart78AnomalySplittingTorsorCardinality

/-- Finite function spaces have the expected cardinality.
    thm:xi-time-part78-anomaly-splitting-torsor-cardinality -/
theorem xi_time_part78_anomaly_splitting_torsor_cardinality_finite_function_cardinality
    (a b : ℕ) :
    Fintype.card (Fin a → Fin b) = b ^ a := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- In wedge rank at most one, the splitting torsor has a single point.
    thm:xi-time-part78-anomaly-splitting-torsor-cardinality -/
theorem xi_time_part78_anomaly_splitting_torsor_cardinality_rank_le_one_singleton
    (r Fcard wedgeFcard : ℕ) (hr : r ≤ 1) :
    Fintype.card (Fin (Nat.choose r 2) → Fin (Fcard ^ r * wedgeFcard)) = 1 := by
  have hchoose : Nat.choose r 2 = 0 := by
    interval_cases r <;> simp
  simp [hchoose]

/-- A singleton defect ledger gives a singleton splitting torsor.
    thm:xi-time-part78-anomaly-splitting-torsor-cardinality -/
theorem xi_time_part78_anomaly_splitting_torsor_cardinality_trivial_ledger_singleton
    (r Fcard wedgeFcard : ℕ) (hledger : Fcard ^ r * wedgeFcard = 1) :
    Fintype.card (Fin (Nat.choose r 2) → Fin (Fcard ^ r * wedgeFcard)) = 1 := by
  simp [hledger]

/-- Paper theorem: the splitting torsor is modeled by functions from the wedge-rank index
set into the finite defect ledger. -/
theorem paper_xi_time_part78_anomaly_splitting_torsor_cardinality (r Fcard wedgeFcard : ℕ) :
    Fintype.card (Fin (Nat.choose r 2) → Fin (Fcard ^ r * wedgeFcard)) =
      (Fcard ^ r * wedgeFcard) ^ Nat.choose r 2 := by
  exact xi_time_part78_anomaly_splitting_torsor_cardinality_finite_function_cardinality
    (Nat.choose r 2) (Fcard ^ r * wedgeFcard)

end Omega.Zeta.XiTimePart78AnomalySplittingTorsorCardinality
