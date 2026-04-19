import Mathlib.Tactic

namespace Omega.POM.SufficientStatisticResidualNoninvertibility

/-- A residual taking values in `Fin (d_x + 1)` cannot be injective on a larger finite type.
    prop:pom-sufficient-statistic-residual-noninvertibility -/
theorem paper_pom_sufficient_statistic_residual_noninvertibility {Ω : Type*} [Fintype Ω]
    (d_x : ℕ) (ℛ : Ω → Fin (d_x + 1)) (hbig : d_x + 1 < Fintype.card Ω) :
    ¬ Function.Injective ℛ := by
  intro hℛ
  have hcard : Fintype.card Ω ≤ d_x + 1 := by
    simpa using Fintype.card_le_of_injective ℛ hℛ
  exact (Nat.not_lt_of_ge hcard) hbig

end Omega.POM.SufficientStatisticResidualNoninvertibility
