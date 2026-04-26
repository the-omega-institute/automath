import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.DiagonalRateAcceptRefreshSSTStrong

open scoped BigOperators

namespace Omega.POM

/-- Accepted law induced by an accept-refresh stopping rule `a`. -/
def pom_diagonal_rate_refresh_accept_uniqueness_optimality_accepted_law
    (D : DiagonalRateAcceptRefreshSSTStrongData) (a : D.State → ℝ) (y : D.State) : ℝ :=
  a y * D.rδ y

/-- The only stopping rule whose accepted law is the constant value `θ`. -/
noncomputable def pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule
    (D : DiagonalRateAcceptRefreshSSTStrongData) (θ : ℝ) (y : D.State) : ℝ :=
  θ / D.rδ y

/-- A concrete surrogate for the expected number of refreshes under the diagonal rule. -/
noncomputable def pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_refresh_count
    (D : DiagonalRateAcceptRefreshSSTStrongData) (θ : ℝ) : ℝ :=
  θ * ∑ y, (1 / D.rδ y : ℝ)

/-- The stopping-time surrogate differs from the refresh count by the initial accepted step. -/
noncomputable def pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_stopping_time
    (D : DiagonalRateAcceptRefreshSSTStrongData) (θ : ℝ) : ℝ :=
  1 + pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_refresh_count D θ

/-- Paper label: `prop:pom-diagonal-rate-refresh-accept-uniqueness-optimality`. The accepted-law
constraint determines the stopping rule uniquely as `a(y) = θ / rδ(y)`. The strong-stationary-time
package remains available from the exact accept-refresh wrapper, and the concrete expected refresh
count / stopping-time surrogates are monotone in `θ`, hence minimized at the smallest admissible
value `c`. -/
theorem paper_pom_diagonal_rate_refresh_accept_uniqueness_optimality
    (D : DiagonalRateAcceptRefreshSSTStrongData) (θ c : ℝ)
    (hθ : 0 < θ) (hc : 0 < c) (hcθ : c ≤ θ) :
    D.strongStationaryTime ∧
      (∃! a : D.State → ℝ,
        ∀ y, pom_diagonal_rate_refresh_accept_uniqueness_optimality_accepted_law D a y = θ) ∧
      (∀ a : D.State → ℝ,
        (∀ y, pom_diagonal_rate_refresh_accept_uniqueness_optimality_accepted_law D a y = θ) ↔
          a = pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule D θ) ∧
      (∀ y, 0 < pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule D θ y) ∧
      (∀ y, 0 < pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule D c y) ∧
      pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_refresh_count D c ≤
        pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_refresh_count D θ ∧
      pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_stopping_time D c ≤
        pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_stopping_time D θ := by
  have hsst := (paper_pom_diagonal_rate_accept_refresh_sst_strong D).1
  have hcanonical :
      ∀ y,
        pom_diagonal_rate_refresh_accept_uniqueness_optimality_accepted_law D
            (pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule D θ) y =
          θ := by
    intro y
    have hr_ne : D.rδ y ≠ 0 := by linarith [D.rδ_pos y]
    unfold pom_diagonal_rate_refresh_accept_uniqueness_optimality_accepted_law
      pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule
    field_simp [hr_ne]
  have hunique_rule :
      ∃! a : D.State → ℝ,
        ∀ y, pom_diagonal_rate_refresh_accept_uniqueness_optimality_accepted_law D a y = θ := by
    refine ⟨pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule D θ,
      hcanonical, ?_⟩
    intro a ha
    funext y
    have hr_ne : D.rδ y ≠ 0 := by linarith [D.rδ_pos y]
    exact (eq_div_iff hr_ne).2 (by
      simpa [pom_diagonal_rate_refresh_accept_uniqueness_optimality_accepted_law] using ha y)
  rcases hunique_rule with ⟨a0, ha0, huniq0⟩
  have hcharacterize :
      ∀ a : D.State → ℝ,
        (∀ y, pom_diagonal_rate_refresh_accept_uniqueness_optimality_accepted_law D a y = θ) ↔
          a = pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule D θ := by
    intro a
    constructor
    · intro ha
      have haeq : a = a0 := huniq0 a ha
      have hcanon : pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule D θ = a0 :=
        huniq0
          (pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule D θ)
          hcanonical
      calc
        a = a0 := haeq
        _ = pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule D θ := hcanon.symm
    · intro ha
      simpa [ha] using hcanonical
  have hθ_pos_rule :
      ∀ y, 0 < pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule D θ y := by
    intro y
    unfold pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule
    exact div_pos hθ (D.rδ_pos y)
  have hc_pos_rule :
      ∀ y, 0 < pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule D c y := by
    intro y
    unfold pom_diagonal_rate_refresh_accept_uniqueness_optimality_canonical_rule
    exact div_pos hc (D.rδ_pos y)
  have hsum_nonneg : 0 ≤ ∑ y, (1 / D.rδ y : ℝ) := by
    refine Finset.sum_nonneg ?_
    intro y hy
    exact le_of_lt (one_div_pos.mpr (D.rδ_pos y))
  have hrefresh_mono :
      pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_refresh_count D c ≤
        pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_refresh_count D θ := by
    unfold pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_refresh_count
    nlinarith
  have htime_mono :
      pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_stopping_time D c ≤
        pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_stopping_time D θ := by
    unfold pom_diagonal_rate_refresh_accept_uniqueness_optimality_expected_stopping_time
    nlinarith [hrefresh_mono]
  exact ⟨hsst, ⟨a0, ha0, huniq0⟩, hcharacterize, hθ_pos_rule, hc_pos_rule, hrefresh_mono,
    htime_mono⟩

end Omega.POM
