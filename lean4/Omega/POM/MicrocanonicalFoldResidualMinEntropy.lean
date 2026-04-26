import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.POM.DiagonalRateSchurConcavity
import Omega.POM.MicrocanonicalFoldHtFromPowerSums

namespace Omega.POM

open scoped BigOperators

/-- Residual min-entropy proxy obtained from the degree-`2` microcanonical fold coefficient. -/
noncomputable def pom_microcanonical_fold_residual_min_entropy_residual
    {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  -Real.log (pom_microcanonical_fold_ht_from_power_sums_h2 w)

/-- Paper label: `thm:pom-microcanonical-fold-residual-min-entropy`. For a finite probability
vector, the low-order coefficient formula gives `h₂(w) = (1 + p₂(w)) / 2`; since `0 ≤ p₂(w) ≤ 1`,
the residual quantity `-log h₂(w)` is nonnegative, and it vanishes in the extremal case
`p₂(w) = 1`. -/
theorem paper_pom_microcanonical_fold_residual_min_entropy
    {n : ℕ} (w : Fin n → ℝ) (hw : IsProbabilityVector w) :
    pom_microcanonical_fold_residual_min_entropy_residual w =
        -Real.log
          ((1 + pom_microcanonical_fold_ht_from_power_sums_powerSum w 2) / 2) ∧
      0 ≤ pom_microcanonical_fold_residual_min_entropy_residual w ∧
      (pom_microcanonical_fold_ht_from_power_sums_powerSum w 2 = 1 →
        pom_microcanonical_fold_residual_min_entropy_residual w = 0) := by
  rcases hw with ⟨hw_nonneg, hw_sum⟩
  have h₁ : pom_microcanonical_fold_ht_from_power_sums_powerSum w 1 = 1 := by
    simpa [pom_microcanonical_fold_ht_from_power_sums_powerSum] using hw_sum
  have hh₂ :
      pom_microcanonical_fold_ht_from_power_sums_h2 w =
        (1 + pom_microcanonical_fold_ht_from_power_sums_powerSum w 2) / 2 :=
    (paper_pom_microcanonical_fold_ht_from_power_sums w h₁).1
  have hcoord_le_one : ∀ i : Fin n, w i ≤ 1 := by
    intro i
    have hi :
        w i ≤ ∑ j : Fin n, w j := by
      simpa using
        (Finset.single_le_sum
          (fun j _ => hw_nonneg j)
          (by simp : i ∈ (Finset.univ : Finset (Fin n))))
    simpa [hw_sum] using hi
  have hp₂_nonneg : 0 ≤ pom_microcanonical_fold_ht_from_power_sums_powerSum w 2 := by
    unfold pom_microcanonical_fold_ht_from_power_sums_powerSum
    exact Finset.sum_nonneg (fun i _ => by positivity)
  have hp₂_le_one : pom_microcanonical_fold_ht_from_power_sums_powerSum w 2 ≤ 1 := by
    calc
      pom_microcanonical_fold_ht_from_power_sums_powerSum w 2
          = ∑ i : Fin n, w i ^ (2 : ℕ) := rfl
      _ ≤ ∑ i : Fin n, w i := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have h0 : 0 ≤ w i := hw_nonneg i
            have h1 : w i ≤ 1 := hcoord_le_one i
            nlinarith [h0, h1]
      _ = 1 := hw_sum
  have hh₂_pos : 0 < pom_microcanonical_fold_ht_from_power_sums_h2 w := by
    rw [hh₂]
    linarith
  have hh₂_le_one : pom_microcanonical_fold_ht_from_power_sums_h2 w ≤ 1 := by
    rw [hh₂]
    linarith
  have hlog_nonpos : Real.log (pom_microcanonical_fold_ht_from_power_sums_h2 w) ≤ 0 :=
    Real.log_nonpos hh₂_pos.le hh₂_le_one
  refine ⟨by simp [pom_microcanonical_fold_residual_min_entropy_residual, hh₂], ?_, ?_⟩
  · simpa [pom_microcanonical_fold_residual_min_entropy_residual] using neg_nonneg.mpr hlog_nonpos
  · intro hp₂_eq_one
    rw [pom_microcanonical_fold_residual_min_entropy_residual, hh₂, hp₂_eq_one]
    norm_num

end Omega.POM
