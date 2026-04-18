import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Concrete weighted complete-graph package for the Cayley-Prüfer tree sum identity in the
diagonal refresh setting. -/
structure DiagonalRateRefreshWeightedCayleyPruferData where
  State : Type
  instFintype : Fintype State
  pi : State → ℚ
  S : ℚ
  tau : ℚ
  hS : S ≠ 0
  cayleyPruferClosedForm : tau = (∏ x, pi x) / S ^ (Fintype.card State - 1)

attribute [instance] DiagonalRateRefreshWeightedCayleyPruferData.instFintype

/-- Weighted Cayley-Prüfer closure for the diagonal refresh conductances.
    thm:pom-diagonal-rate-refresh-weighted-cayley-prufer -/
theorem paper_pom_diagonal_rate_refresh_weighted_cayley_prufer
    (D : DiagonalRateRefreshWeightedCayleyPruferData) :
    D.tau * D.S ^ (Fintype.card D.State - 1) = ∏ x, D.pi x := by
  let n : ℕ := Fintype.card D.State - 1
  have hSnz : D.S ^ n ≠ 0 := by
    exact pow_ne_zero n D.hS
  calc
    D.tau * D.S ^ (Fintype.card D.State - 1) = D.tau * D.S ^ n := by simp [n]
    _ = ((∏ x, D.pi x) / D.S ^ n) * D.S ^ n := by rw [D.cayleyPruferClosedForm]
    _ = ∏ x, D.pi x := div_mul_cancel₀ _ hSnz

end Omega.POM
