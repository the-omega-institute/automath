import Mathlib.Tactic
import Omega.Folding.FoldBinGaugeVolumeStirling

namespace Omega.Conclusion

open Omega.Folding

/-- Singleton fiber profile with total mass `2^m`. -/
def conclusion_binfold_gauge_volume_double_exponential_law_profile (m : ℕ) : Unit → ℕ :=
  fun _ => 2 ^ m

/-- First-order entropy term `κ_m` in the singleton binfold model. -/
noncomputable def conclusion_binfold_gauge_volume_double_exponential_law_kappa (m : ℕ) : ℝ :=
  binGaugeKappa m (conclusion_binfold_gauge_volume_double_exponential_law_profile m)

/-- Normalized logarithmic gauge volume `g_m` in the singleton binfold model. -/
noncomputable def conclusion_binfold_gauge_volume_double_exponential_law_g (m : ℕ) : ℝ :=
  binGaugeG m (conclusion_binfold_gauge_volume_double_exponential_law_profile m)

/-- Exponential gauge volume reconstructed from the normalized log-volume. -/
noncomputable def conclusion_binfold_gauge_volume_double_exponential_law_volume (m : ℕ) : ℝ :=
  Real.exp
    ((2 : ℝ) ^ m * conclusion_binfold_gauge_volume_double_exponential_law_g m)

/-- In the singleton model the first-order term is exactly `m log 2`, while the normalized
log-volume differs from `κ_m - 1` by a concrete exponentially decaying remainder. -/
def conclusion_binfold_gauge_volume_double_exponential_law_statement (m : ℕ) : Prop :=
  ∃ E : ℝ,
    0 ≤ E ∧
      E ≤ (Real.log (2 * Real.pi) / 2 + (m : ℝ) * Real.log 2 + 1 / 12) / (2 : ℝ) ^ m ∧
      conclusion_binfold_gauge_volume_double_exponential_law_kappa m = (m : ℝ) * Real.log 2 ∧
      conclusion_binfold_gauge_volume_double_exponential_law_g m =
        conclusion_binfold_gauge_volume_double_exponential_law_kappa m - 1 + E ∧
      Real.log (conclusion_binfold_gauge_volume_double_exponential_law_volume m) =
        (2 : ℝ) ^ m * ((m : ℝ) * Real.log 2 - 1 + E)

/-- Paper label: `thm:conclusion-binfold-gauge-volume-double-exponential-law`. -/
theorem paper_conclusion_binfold_gauge_volume_double_exponential_law (m : ℕ) :
    conclusion_binfold_gauge_volume_double_exponential_law_statement m := by
  have hhd : ∀ u : Unit, 1 ≤ conclusion_binfold_gauge_volume_double_exponential_law_profile m u := by
    intro u
    exact Nat.succ_le_of_lt (by
      simpa [conclusion_binfold_gauge_volume_double_exponential_law_profile] using
        Nat.pow_pos (by decide : 0 < 2) m)
  have hsum :
      ∑ u, conclusion_binfold_gauge_volume_double_exponential_law_profile m u = 2 ^ m := by
    simp [conclusion_binfold_gauge_volume_double_exponential_law_profile]
  rcases paper_fold_bin_gauge_volume_stirling m
      (conclusion_binfold_gauge_volume_double_exponential_law_profile m) hhd hsum with
    ⟨E, hE_nonneg, hE_le, hG_eq⟩
  have hG :
      conclusion_binfold_gauge_volume_double_exponential_law_g m =
        conclusion_binfold_gauge_volume_double_exponential_law_kappa m - 1 + E := by
    simpa [conclusion_binfold_gauge_volume_double_exponential_law_g,
      conclusion_binfold_gauge_volume_double_exponential_law_kappa] using hG_eq
  refine ⟨E, hE_nonneg, ?_, ?_, hG, ?_⟩
  · simpa using hE_le
  · have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
    have hpow_ne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt hpow_pos
    calc
      conclusion_binfold_gauge_volume_double_exponential_law_kappa m
          = ((((2 ^ m : ℕ) : ℝ) * Real.log ((2 ^ m : ℕ) : ℝ)) / (2 : ℝ) ^ m) := by
              simp [conclusion_binfold_gauge_volume_double_exponential_law_kappa,
                binGaugeKappa, conclusion_binfold_gauge_volume_double_exponential_law_profile]
      _ = (((2 : ℝ) ^ m) * Real.log ((2 : ℝ) ^ m)) / (2 : ℝ) ^ m := by
            norm_num
      _ = Real.log ((2 : ℝ) ^ m) := by
            field_simp [hpow_ne]
      _ = (m : ℝ) * Real.log 2 := by
            rw [← Real.rpow_natCast, Real.log_rpow (by positivity)]
  · rw [conclusion_binfold_gauge_volume_double_exponential_law_volume, Real.log_exp]
    calc
      (2 : ℝ) ^ m * conclusion_binfold_gauge_volume_double_exponential_law_g m
          = (2 : ℝ) ^ m *
              (conclusion_binfold_gauge_volume_double_exponential_law_kappa m - 1 + E) := by
                rw [hG]
      _ = (2 : ℝ) ^ m * ((m : ℝ) * Real.log 2 - 1 + E) := by
            rw [show conclusion_binfold_gauge_volume_double_exponential_law_kappa m =
                (m : ℝ) * Real.log 2 by
              have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
              have hpow_ne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt hpow_pos
              calc
                conclusion_binfold_gauge_volume_double_exponential_law_kappa m
                    = ((((2 ^ m : ℕ) : ℝ) * Real.log ((2 ^ m : ℕ) : ℝ)) / (2 : ℝ) ^ m) := by
                        simp [conclusion_binfold_gauge_volume_double_exponential_law_kappa,
                          binGaugeKappa,
                          conclusion_binfold_gauge_volume_double_exponential_law_profile]
                _ = (((2 : ℝ) ^ m) * Real.log ((2 : ℝ) ^ m)) / (2 : ℝ) ^ m := by
                      norm_num
                _ = Real.log ((2 : ℝ) ^ m) := by
                      field_simp [hpow_ne]
                _ = (m : ℝ) * Real.log 2 := by
                      rw [← Real.rpow_natCast, Real.log_rpow (by positivity)]]

end Omega.Conclusion
