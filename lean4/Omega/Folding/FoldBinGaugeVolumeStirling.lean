import Mathlib.Tactic
import Omega.Folding.BinGaugeVolume

open scoped BigOperators

namespace Omega.Folding

/-- The first-order Stirling expansion for the normalized bin-gauge volume: after extracting the
main term `κ_m` and the exact `-1` contribution from `∑_w d_m(w) = 2^m`, the leftover correction
is bounded by an explicit `|X_m| m / 2^m`-scale quantity. -/
theorem paper_fold_bin_gauge_volume_stirling {alpha : Type} [Fintype alpha]
    (m : ℕ) (d : alpha → ℕ) (hd : ∀ a, 1 ≤ d a) (hsum : ∑ a, d a = 2 ^ m) :
    ∃ E : ℝ,
      0 ≤ E ∧
        E ≤
            ((Fintype.card alpha : ℝ) *
                (Real.log (2 * Real.pi) / 2 + (m : ℝ) * Real.log 2 + 1 / 12)) /
              (2 : ℝ) ^ m ∧
          binGaugeG m d = binGaugeKappa m d - 1 + E := by
  classical
  have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
  have hpow_ne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt hpow_pos
  have hsumR : (∑ a, (d a : ℝ)) = (2 : ℝ) ^ m := by
    exact_mod_cast hsum
  rcases (paper_fold_bin_gauge_volume_stirling_second_order (alpha := alpha) d hd) with
      ⟨R, hR_nonneg, hR_le, hR_eq⟩
  let E : ℝ :=
    ((1 / 2 : ℝ) *
        ((Fintype.card alpha : ℝ) * Real.log (2 * Real.pi) + ∑ a, Real.log (d a)) + R) /
      (2 : ℝ) ^ m
  have hlog_nonneg : 0 ≤ ∑ a, Real.log (d a) := by
    exact Finset.sum_nonneg fun a _ => Real.log_nonneg (by exact_mod_cast hd a)
  have htwo_pi_nonneg : 0 ≤ Real.log (2 * Real.pi) := by
    linarith [log_two_pi_ge_eleven_sixths]
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    positivity
  have hd_le_pow : ∀ a, d a ≤ 2 ^ m := by
    intro a
    have hsingle : d a ≤ ∑ b, d b := by
      simpa using Finset.single_le_sum (fun b _ => Nat.zero_le (d b)) (by simp : a ∈ Finset.univ)
    exact hsingle.trans (by simp [hsum])
  have hlog_le : ∀ a, Real.log (d a) ≤ (m : ℝ) * Real.log 2 := by
    intro a
    have hda_pos : 0 < (d a : ℝ) := by
      exact_mod_cast hd a
    have hda_le : (d a : ℝ) ≤ (2 : ℝ) ^ m := by
      exact_mod_cast hd_le_pow a
    calc
      Real.log (d a) ≤ Real.log ((2 : ℝ) ^ m) := Real.log_le_log hda_pos hda_le
      _ = (m : ℝ) * Real.log 2 := by
        rw [← Real.rpow_natCast, Real.log_rpow (by positivity)]
  have hsum_log_le : ∑ a, Real.log (d a) ≤ (Fintype.card alpha : ℝ) * ((m : ℝ) * Real.log 2) := by
    calc
      ∑ a, Real.log (d a) ≤ ∑ a, (m : ℝ) * Real.log 2 := by
        exact Finset.sum_le_sum fun a _ => hlog_le a
      _ = (Fintype.card alpha : ℝ) * ((m : ℝ) * Real.log 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hE_le :
      E ≤
        ((Fintype.card alpha : ℝ) *
            (Real.log (2 * Real.pi) / 2 + (m : ℝ) * Real.log 2 + 1 / 12)) /
          (2 : ℝ) ^ m := by
    dsimp [E]
    refine (div_le_div_iff_of_pos_right hpow_pos).2 ?_
    nlinarith
  refine ⟨E, hE_nonneg, hE_le, ?_⟩
  dsimp [E, binGaugeG, binGaugeKappa, binGaugeLogVolume]
  rw [hR_eq, Finset.sum_sub_distrib, hsumR]
  field_simp [hpow_ne]
  ring

end Omega.Folding
