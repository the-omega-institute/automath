import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

section

variable {α : Type*} [Fintype α]

/-- The `k`-th power sum `p_k(w) = ∑_x w(x)^k`. -/
def pom_microcanonical_fold_ht_from_power_sums_powerSum (w : α → ℝ) (k : ℕ) : ℝ :=
  ∑ x : α, w x ^ k

/-- The degree-`k` logarithmic coefficient `p_k(w) / k` coming from
`-log (1 - u) = ∑_{k≥1} u^k / k`. -/
noncomputable def pom_microcanonical_fold_ht_from_power_sums_logCoeff (w : α → ℝ) (k : ℕ) : ℝ :=
  pom_microcanonical_fold_ht_from_power_sums_powerSum w k / (k : ℝ)

/-- The degree-`2` coefficient obtained by truncating
`exp (∑_{k=1}^∞ p_k(w) z^k / k)`. -/
noncomputable def pom_microcanonical_fold_ht_from_power_sums_h2 (w : α → ℝ) : ℝ :=
  pom_microcanonical_fold_ht_from_power_sums_logCoeff w 2 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 1 ^ 2 / 2

/-- The degree-`3` coefficient obtained by truncating the exponential series. -/
noncomputable def pom_microcanonical_fold_ht_from_power_sums_h3 (w : α → ℝ) : ℝ :=
  pom_microcanonical_fold_ht_from_power_sums_logCoeff w 3 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 1 *
      pom_microcanonical_fold_ht_from_power_sums_logCoeff w 2 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 1 ^ 3 / 6

/-- The degree-`4` coefficient obtained by truncating the exponential series. -/
noncomputable def pom_microcanonical_fold_ht_from_power_sums_h4 (w : α → ℝ) : ℝ :=
  pom_microcanonical_fold_ht_from_power_sums_logCoeff w 4 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 1 *
      pom_microcanonical_fold_ht_from_power_sums_logCoeff w 3 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 2 ^ 2 / 2 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 1 ^ 2 *
      pom_microcanonical_fold_ht_from_power_sums_logCoeff w 2 / 2 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 1 ^ 4 / 24

/-- The degree-`5` coefficient obtained by truncating the exponential series. -/
noncomputable def pom_microcanonical_fold_ht_from_power_sums_h5 (w : α → ℝ) : ℝ :=
  pom_microcanonical_fold_ht_from_power_sums_logCoeff w 5 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 1 *
      pom_microcanonical_fold_ht_from_power_sums_logCoeff w 4 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 2 *
      pom_microcanonical_fold_ht_from_power_sums_logCoeff w 3 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 1 ^ 2 *
      pom_microcanonical_fold_ht_from_power_sums_logCoeff w 3 / 2 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 1 *
      pom_microcanonical_fold_ht_from_power_sums_logCoeff w 2 ^ 2 / 2 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 1 ^ 3 *
      pom_microcanonical_fold_ht_from_power_sums_logCoeff w 2 / 6 +
    pom_microcanonical_fold_ht_from_power_sums_logCoeff w 1 ^ 5 / 120

/-- Paper label: `thm:pom-microcanonical-fold-ht-from-power-sums`. Writing
`log 𝓗_w(z) = ∑_{k≥1} p_k(w) z^k / k` and truncating the exponential series shows that the first
nontrivial `h_t` depend only on the corresponding power sums; once `p₁(w)=1`, the coefficients
reduce to the explicit low-order formulas. -/
theorem paper_pom_microcanonical_fold_ht_from_power_sums (w : α → ℝ)
    (h₁ : pom_microcanonical_fold_ht_from_power_sums_powerSum w 1 = 1) :
    pom_microcanonical_fold_ht_from_power_sums_h2 w =
        (1 + pom_microcanonical_fold_ht_from_power_sums_powerSum w 2) / 2 ∧
      pom_microcanonical_fold_ht_from_power_sums_h3 w =
        (1 + 3 * pom_microcanonical_fold_ht_from_power_sums_powerSum w 2 +
            2 * pom_microcanonical_fold_ht_from_power_sums_powerSum w 3) / 6 ∧
      pom_microcanonical_fold_ht_from_power_sums_h4 w =
        (1 + 6 * pom_microcanonical_fold_ht_from_power_sums_powerSum w 2 +
            3 * pom_microcanonical_fold_ht_from_power_sums_powerSum w 2 ^ 2 +
            8 * pom_microcanonical_fold_ht_from_power_sums_powerSum w 3 +
            6 * pom_microcanonical_fold_ht_from_power_sums_powerSum w 4) / 24 ∧
      pom_microcanonical_fold_ht_from_power_sums_h5 w =
        (1 + 10 * pom_microcanonical_fold_ht_from_power_sums_powerSum w 2 +
            15 * pom_microcanonical_fold_ht_from_power_sums_powerSum w 2 ^ 2 +
            20 * pom_microcanonical_fold_ht_from_power_sums_powerSum w 3 +
            20 * pom_microcanonical_fold_ht_from_power_sums_powerSum w 2 *
              pom_microcanonical_fold_ht_from_power_sums_powerSum w 3 +
            30 * pom_microcanonical_fold_ht_from_power_sums_powerSum w 4 +
            24 * pom_microcanonical_fold_ht_from_power_sums_powerSum w 5) / 120 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold pom_microcanonical_fold_ht_from_power_sums_h2
      pom_microcanonical_fold_ht_from_power_sums_logCoeff
    rw [h₁]
    ring
  · unfold pom_microcanonical_fold_ht_from_power_sums_h3
      pom_microcanonical_fold_ht_from_power_sums_logCoeff
    rw [h₁]
    ring
  · unfold pom_microcanonical_fold_ht_from_power_sums_h4
      pom_microcanonical_fold_ht_from_power_sums_logCoeff
    rw [h₁]
    ring
  · unfold pom_microcanonical_fold_ht_from_power_sums_h5
      pom_microcanonical_fold_ht_from_power_sums_logCoeff
    rw [h₁]
    ring

end

end Omega.POM
