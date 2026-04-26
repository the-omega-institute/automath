import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.POM.DiagonalRateRefreshRenewalCoding

namespace Omega.POM

open scoped BigOperators

/-- Concrete data for the length-biased stationary law in the diagonal refresh model. The
regeneration structure is packaged by the renewal-coding witness, while the base refresh law and
the state-dependent refresh rates determine the block occupation profile. -/
structure pom_diagonal_rate_refresh_length_biased_stationary_data where
  State : Type
  instFintypeState : Fintype State
  instDecidableEqState : DecidableEq State
  renewalWitness : pom_diagonal_rate_refresh_renewal_coding_witness State
  refreshBaseMass : State → ℚ
  refreshRate : State → ℚ
  refreshRate_ne_zero : ∀ x, refreshRate x ≠ 0

attribute [instance] pom_diagonal_rate_refresh_length_biased_stationary_data.instFintypeState
attribute [instance] pom_diagonal_rate_refresh_length_biased_stationary_data.instDecidableEqState

/-- Expected holding time in state `x` during one regeneration block. -/
def pom_diagonal_rate_refresh_length_biased_stationary_expected_holding
    (D : pom_diagonal_rate_refresh_length_biased_stationary_data) (x : D.State) : ℚ :=
  1 / D.refreshRate x

/-- Expected occupation mass contributed by state `x` over one regeneration block. -/
def pom_diagonal_rate_refresh_length_biased_stationary_occupation_mass
    (D : pom_diagonal_rate_refresh_length_biased_stationary_data) (x : D.State) : ℚ :=
  D.refreshBaseMass x / D.refreshRate x

/-- Total expected occupation time of one regeneration block. -/
def pom_diagonal_rate_refresh_length_biased_stationary_total_occupation_mass
    (D : pom_diagonal_rate_refresh_length_biased_stationary_data) : ℚ :=
  ∑ x, pom_diagonal_rate_refresh_length_biased_stationary_occupation_mass D x

/-- Stationary mass obtained by normalizing occupation time over one regeneration block. -/
def pom_diagonal_rate_refresh_length_biased_stationary_stationary_mass
    (D : pom_diagonal_rate_refresh_length_biased_stationary_data) (x : D.State) : ℚ :=
  pom_diagonal_rate_refresh_length_biased_stationary_occupation_mass D x /
    pom_diagonal_rate_refresh_length_biased_stationary_total_occupation_mass D

/-- The displayed `t`-closed form, where `t(x) = 1 / r(x)`. -/
def pom_diagonal_rate_refresh_length_biased_stationary_t_closed_form
    (D : pom_diagonal_rate_refresh_length_biased_stationary_data) (x : D.State) : ℚ :=
  (D.refreshBaseMass x / D.refreshRate x) /
    (∑ z, D.refreshBaseMass z / D.refreshRate z)

/-- Concrete paper-facing formulation of the length-biased stationary law. -/
def pom_diagonal_rate_refresh_length_biased_stationary_statement
    (D : pom_diagonal_rate_refresh_length_biased_stationary_data) : Prop :=
  pom_diagonal_rate_refresh_renewal_coding_statement D.renewalWitness ∧
    (∀ x,
      pom_diagonal_rate_refresh_length_biased_stationary_expected_holding D x =
        1 / D.refreshRate x) ∧
    (∀ x,
      pom_diagonal_rate_refresh_length_biased_stationary_occupation_mass D x =
        D.refreshBaseMass x *
          pom_diagonal_rate_refresh_length_biased_stationary_expected_holding D x) ∧
    (∀ x,
      pom_diagonal_rate_refresh_length_biased_stationary_stationary_mass D x =
        pom_diagonal_rate_refresh_length_biased_stationary_occupation_mass D x /
          pom_diagonal_rate_refresh_length_biased_stationary_total_occupation_mass D) ∧
    ∀ x,
      pom_diagonal_rate_refresh_length_biased_stationary_stationary_mass D x =
        pom_diagonal_rate_refresh_length_biased_stationary_t_closed_form D x

/-- Paper label: `cor:pom-diagonal-rate-refresh-length-biased-stationary`. Renewal coding gives
the regeneration blocks, the expected holding time in state `x` is `1 / r(x)`, and normalizing the
expected occupation mass over one block yields the length-biased stationary law in the displayed
`t`-closed form. -/
theorem paper_pom_diagonal_rate_refresh_length_biased_stationary
    (D : pom_diagonal_rate_refresh_length_biased_stationary_data) :
    pom_diagonal_rate_refresh_length_biased_stationary_statement D := by
  refine ⟨paper_pom_diagonal_rate_refresh_renewal_coding (w := D.renewalWitness), ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rw [pom_diagonal_rate_refresh_length_biased_stationary_occupation_mass,
      div_eq_mul_inv]
    simp [pom_diagonal_rate_refresh_length_biased_stationary_expected_holding]
  · intro x
    rfl
  · intro x
    rfl

end Omega.POM
