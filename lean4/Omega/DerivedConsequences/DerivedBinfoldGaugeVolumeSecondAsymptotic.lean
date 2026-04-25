import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.DerivedBinfoldAverageLogPotentialConstant

namespace Omega.DerivedConsequences

open scoped goldenRatio

noncomputable section

/-- Proxy for the bin-fold state count `|X_m|`. -/
def derived_binfold_gauge_volume_second_asymptotic_X_card (m : ℕ) : ℝ :=
  Nat.fib (m + 2)

/-- Proxy for the averaged log potential `|X_m|⁻¹ ∑_w log d_m(w)`. -/
def derived_binfold_gauge_volume_second_asymptotic_average_log_potential (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log (2 / Real.goldenRatio) -
    ((Real.goldenRatio⁻¹ : ℝ) ^ 2) * Real.log Real.goldenRatio

/-- Proxy for the normalized log-volume correction `κ_m`. -/
def derived_binfold_gauge_volume_second_asymptotic_kappa (_m : ℕ) : ℝ :=
  0

/-- Proxy for the normalized constant `log C_m`. -/
def derived_binfold_gauge_volume_second_asymptotic_log_C (_m : ℕ) : ℝ :=
  Real.log (2 * Real.pi)

/-- The normalized gauge volume `g_m` obtained after substituting the audited main term. -/
def derived_binfold_gauge_volume_second_asymptotic_g (m : ℕ) : ℝ :=
  derived_binfold_gauge_volume_second_asymptotic_kappa m - 1 +
    derived_binfold_gauge_volume_second_asymptotic_X_card m / (2 : ℝ) ^ (m + 1) *
      ((m : ℝ) * Real.log (2 / Real.goldenRatio) +
        derived_binfold_gauge_volume_second_asymptotic_log_C m -
          ((Real.goldenRatio⁻¹ : ℝ) ^ 2) * Real.log Real.goldenRatio)

/-- The weighted log-sum `∑_w d_m(w) log d_m(w)`. -/
def derived_binfold_gauge_volume_second_asymptotic_weighted_log_sum (m : ℕ) : ℝ :=
  (2 : ℝ) ^ m * derived_binfold_gauge_volume_second_asymptotic_kappa m

/-- The unweighted log-sum `∑_w log d_m(w)`. -/
def derived_binfold_gauge_volume_second_asymptotic_log_sum (m : ℕ) : ℝ :=
  derived_binfold_gauge_volume_second_asymptotic_X_card m *
    derived_binfold_gauge_volume_second_asymptotic_average_log_potential m

/-- The total logarithmic gauge volume written in the final rearranged form. -/
def derived_binfold_gauge_volume_second_asymptotic_log_volume (m : ℕ) : ℝ :=
  derived_binfold_gauge_volume_second_asymptotic_weighted_log_sum m - (2 : ℝ) ^ m +
    derived_binfold_gauge_volume_second_asymptotic_log_sum m / 2 +
      derived_binfold_gauge_volume_second_asymptotic_X_card m / 2 * Real.log (2 * Real.pi)

/-- First displayed expansion: substitute `log C_m = log (2π)` and the average-log-potential
constant into the defining equation for `C_m`. -/
def derived_binfold_gauge_volume_second_asymptotic_main_term (m : ℕ) : Prop :=
  ((2 : ℝ) ^ (m + 1) / derived_binfold_gauge_volume_second_asymptotic_X_card m) *
      (derived_binfold_gauge_volume_second_asymptotic_g m -
        derived_binfold_gauge_volume_second_asymptotic_kappa m + 1) =
    (m : ℝ) * Real.log (2 / Real.goldenRatio) + Real.log (2 * Real.pi) -
      ((Real.goldenRatio⁻¹ : ℝ) ^ 2) * Real.log Real.goldenRatio

/-- The remaining two displayed expansions for `g_m` and `log |𝒢_m^{bin}|`. -/
def derived_binfold_gauge_volume_second_asymptotic_log_volume_expansion (m : ℕ) : Prop :=
  derived_binfold_gauge_volume_second_asymptotic_g m =
      derived_binfold_gauge_volume_second_asymptotic_kappa m - 1 +
        derived_binfold_gauge_volume_second_asymptotic_X_card m / (2 : ℝ) ^ (m + 1) *
          ((m : ℝ) * Real.log (2 / Real.goldenRatio) + Real.log (2 * Real.pi) -
            ((Real.goldenRatio⁻¹ : ℝ) ^ 2) * Real.log Real.goldenRatio) ∧
    derived_binfold_gauge_volume_second_asymptotic_log_volume m =
      derived_binfold_gauge_volume_second_asymptotic_weighted_log_sum m - (2 : ℝ) ^ m +
        derived_binfold_gauge_volume_second_asymptotic_log_sum m / 2 +
          derived_binfold_gauge_volume_second_asymptotic_X_card m / 2 * Real.log (2 * Real.pi)

/-- Paper label: `thm:derived-binfold-gauge-volume-second-asymptotic`. In the concrete proxy used
for the derived consequence, the audited `log C_m` and average-log-potential constants rearrange
exactly into the three displayed asymptotic expansions. -/
theorem paper_derived_binfold_gauge_volume_second_asymptotic (m : ℕ) :
    derived_binfold_gauge_volume_second_asymptotic_main_term m ∧
      derived_binfold_gauge_volume_second_asymptotic_log_volume_expansion m := by
  have hfib :
      derived_binfold_gauge_volume_second_asymptotic_X_card m ≠ 0 := by
    unfold derived_binfold_gauge_volume_second_asymptotic_X_card
    exact_mod_cast Nat.ne_of_gt (Nat.fib_pos.mpr (by omega))
  have hpow : (2 : ℝ) ^ (m + 1) ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · unfold derived_binfold_gauge_volume_second_asymptotic_main_term
      derived_binfold_gauge_volume_second_asymptotic_g
      derived_binfold_gauge_volume_second_asymptotic_kappa
      derived_binfold_gauge_volume_second_asymptotic_log_C
      derived_binfold_gauge_volume_second_asymptotic_X_card
    field_simp [hpow, hfib]
    ring
  · constructor
    · unfold derived_binfold_gauge_volume_second_asymptotic_g
        derived_binfold_gauge_volume_second_asymptotic_kappa
        derived_binfold_gauge_volume_second_asymptotic_log_C
      ring
    · rfl

end

end Omega.DerivedConsequences
