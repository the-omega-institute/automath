import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Probability generating function of the first refresh time with refresh rate `r`. -/
def diagonalRateRefreshHoldingPGF (r s : ℚ) : ℚ :=
  r * s / (1 - (1 - r) * s)

/-- Paper label: `lem:pom-diagonal-rate-refresh-holding-time-pgf`. The first refresh time in the
diagonal refresh model is geometric, so its PGF is the standard one-step renewal solution. -/
theorem paper_pom_diagonal_rate_refresh_holding_time_pgf (r s : ℚ)
    (h : 1 - (1 - r) * s ≠ 0) :
    diagonalRateRefreshHoldingPGF r s = r * s / (1 - (1 - r) * s) ∧
      diagonalRateRefreshHoldingPGF r s =
        r * s + (1 - r) * s * diagonalRateRefreshHoldingPGF r s := by
  refine ⟨rfl, ?_⟩
  have hmul : diagonalRateRefreshHoldingPGF r s * (1 - (1 - r) * s) = r * s := by
    simpa [diagonalRateRefreshHoldingPGF] using div_mul_cancel₀ (r * s) h
  calc
    diagonalRateRefreshHoldingPGF r s
        = diagonalRateRefreshHoldingPGF r s * ((1 - (1 - r) * s) + (1 - r) * s) := by
            ring
    _ = diagonalRateRefreshHoldingPGF r s * (1 - (1 - r) * s) +
          (1 - r) * s * diagonalRateRefreshHoldingPGF r s := by
            ring
    _ = r * s + (1 - r) * s * diagonalRateRefreshHoldingPGF r s := by rw [hmul]

/-- Conditional average of the holding-time PGFs over failed refreshes, i.e. over `z ≠ y`. -/
def diagonalRateRefreshFailurePGF {α : Type*} [Fintype α] [DecidableEq α]
    (π : α → ℚ) (y : α) (G : α → ℚ) : ℚ :=
  (∑ z, if z = y then 0 else π z * G z) / (1 - π y)

/-- Renewal factor after a refresh: succeed at `y` now or fail and restart from the averaged
failed refresh state. -/
def diagonalRateRefreshRenewalPGF {α : Type*} [Fintype α] [DecidableEq α]
    (π : α → ℚ) (y : α) (G : α → ℚ) : ℚ :=
  π y / (1 - (1 - π y) * diagonalRateRefreshFailurePGF π y G)

/-- Closed PGF of the hitting time from `x`: first wait for a refresh at `x`, then use the
renewal PGF of the failed refresh rounds. -/
def diagonalRateRefreshClosedHittingPGF {α : Type*} [Fintype α] [DecidableEq α]
    (r π : α → ℚ) (x y : α) (s : ℚ) : ℚ :=
  diagonalRateRefreshHoldingPGF (r x) s *
    diagonalRateRefreshRenewalPGF π y (fun z => diagonalRateRefreshHoldingPGF (r z) s)

/-- In the diagonal refresh model, the first-refresh PGF is geometric, the failed rounds average
into a single renewal factor, and the hitting-time PGF is the resulting closed rational form.
    thm:pom-diagonal-rate-refresh-hitting-time-pgf-closed -/
theorem paper_pom_diagonal_rate_refresh_hitting_time_pgf_closed
    {α : Type*} [Fintype α] [DecidableEq α]
    (r π : α → ℚ) (x y : α) (s : ℚ)
    (hπy : π y ≠ 1)
    (hrenew :
      1 - (1 - π y) *
        diagonalRateRefreshFailurePGF π y (fun z => diagonalRateRefreshHoldingPGF (r z) s) ≠ 0) :
    let G := fun z => diagonalRateRefreshHoldingPGF (r z) s
    let Gbar := diagonalRateRefreshFailurePGF π y G
    let J := diagonalRateRefreshRenewalPGF π y G
    let F := diagonalRateRefreshClosedHittingPGF r π x y s
    J = π y + (1 - π y) * Gbar * J ∧
      F = G x * J ∧
      F = G x * π y / (1 - (1 - π y) * Gbar) := by
  dsimp [diagonalRateRefreshClosedHittingPGF, diagonalRateRefreshRenewalPGF]
  refine ⟨?_, rfl, ?_⟩
  field_simp [hrenew, hπy]
  ring
  ring

end Omega.POM
