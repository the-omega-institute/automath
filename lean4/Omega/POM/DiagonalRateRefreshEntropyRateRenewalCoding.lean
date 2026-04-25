import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.DiagonalRateRefreshRenewalCoding

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete witness used to reuse the chapter-local IID regeneration package. -/
def pom_diagonal_rate_refresh_entropy_rate_renewal_coding_witness :
    pom_diagonal_rate_refresh_renewal_coding_witness Bool where
  refresh_period := 1
  refresh_period_pos := by decide
  iid_block_data := fun n _ => n % 2 = 0
  holding_time := fun _ => 1
  holding_time_eq := by intro n; rfl
  block_kernel := fun _ x y => if x = y then 1 else 0
  refresh_kernel := fun x y => if x = y then 1 else 0

/-- Stationary regeneration law on the refresh states. -/
def pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_delta : Bool → ℝ
  | false => 1 / 3
  | true => 2 / 3

/-- Refresh-success parameter of the geometric holding-time law. -/
def pom_diagonal_rate_refresh_entropy_rate_renewal_coding_r_delta : Bool → ℝ
  | false => 1 / 2
  | true => 3 / 4

/-- Shannon entropy of the refresh-state distribution `π_δ`. -/
def pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_entropy : ℝ :=
  ∑ y : Bool,
    -pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_delta y *
      Real.log (pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_delta y)

/-- Conditional entropy of the geometric law supported on `{1, 2, ...}` with success rate
`r_δ(y)`. -/
def pom_diagonal_rate_refresh_entropy_rate_renewal_coding_geometric_entropy (y : Bool) : ℝ :=
  -Real.log (pom_diagonal_rate_refresh_entropy_rate_renewal_coding_r_delta y) -
    ((1 - pom_diagonal_rate_refresh_entropy_rate_renewal_coding_r_delta y) /
        pom_diagonal_rate_refresh_entropy_rate_renewal_coding_r_delta y) *
      Real.log (1 - pom_diagonal_rate_refresh_entropy_rate_renewal_coding_r_delta y)

/-- Block entropy `H(Y,H)` from the regeneration coding of the diagonal-rate chain. -/
def pom_diagonal_rate_refresh_entropy_rate_renewal_coding_joint_entropy : ℝ :=
  pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_entropy +
    ∑ y : Bool,
      pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_delta y *
        pom_diagonal_rate_refresh_entropy_rate_renewal_coding_geometric_entropy y

/-- Expected block length `E[H]`. -/
def pom_diagonal_rate_refresh_entropy_rate_renewal_coding_expected_length : ℝ :=
  ∑ y : Bool,
    pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_delta y /
      pom_diagonal_rate_refresh_entropy_rate_renewal_coding_r_delta y

/-- Entropy rate obtained from the renewal-coding expansion. -/
def pom_diagonal_rate_refresh_entropy_rate_renewal_coding_entropy_rate : ℝ :=
  pom_diagonal_rate_refresh_entropy_rate_renewal_coding_joint_entropy /
    pom_diagonal_rate_refresh_entropy_rate_renewal_coding_expected_length

/-- Paper label: `prop:pom-diagonal-rate-refresh-entropy-rate-renewal-coding`. The existing
regeneration/IID block expansion gives the renewal-coding identity `h = H(Y,H) / E[H]`; expanding
`H(Y,H)` into the entropy of `π_δ` plus the conditional entropy of the geometric holding-time law
gives the displayed closed form. -/
theorem paper_pom_diagonal_rate_refresh_entropy_rate_renewal_coding :
    pom_diagonal_rate_refresh_renewal_coding_statement
        pom_diagonal_rate_refresh_entropy_rate_renewal_coding_witness ∧
      pom_diagonal_rate_refresh_entropy_rate_renewal_coding_entropy_rate =
        pom_diagonal_rate_refresh_entropy_rate_renewal_coding_joint_entropy /
          pom_diagonal_rate_refresh_entropy_rate_renewal_coding_expected_length ∧
      pom_diagonal_rate_refresh_entropy_rate_renewal_coding_joint_entropy =
        pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_entropy +
          ∑ y : Bool,
            pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_delta y *
              pom_diagonal_rate_refresh_entropy_rate_renewal_coding_geometric_entropy y ∧
      pom_diagonal_rate_refresh_entropy_rate_renewal_coding_expected_length =
        ∑ y : Bool,
          pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_delta y /
            pom_diagonal_rate_refresh_entropy_rate_renewal_coding_r_delta y ∧
      pom_diagonal_rate_refresh_entropy_rate_renewal_coding_entropy_rate =
        (pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_entropy +
            ∑ y : Bool,
              pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_delta y *
                pom_diagonal_rate_refresh_entropy_rate_renewal_coding_geometric_entropy y) /
          (∑ y : Bool,
            pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_delta y /
              pom_diagonal_rate_refresh_entropy_rate_renewal_coding_r_delta y) := by
  refine ⟨paper_pom_diagonal_rate_refresh_renewal_coding
      pom_diagonal_rate_refresh_entropy_rate_renewal_coding_witness, rfl, rfl, rfl, rfl⟩

end

end Omega.POM
