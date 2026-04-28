import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.FullInversionThresholdEntropyGap

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-volume-peak-threshold-separation`. -/
theorem paper_conclusion_volume_peak_threshold_separation {n : ℕ} (hn : 0 < n)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (B : ℕ)
    (hbudget : maxFiberSize d ≤ 2 ^ B) (rhoVol rhoPeak alphaStar : ℝ)
    (hvol : rhoVol = Real.log (2 / Real.goldenRatio) / Real.log 2)
    (hpeak : rhoPeak = alphaStar / Real.log 2)
    (hgap : Real.log (2 / Real.goldenRatio) < alphaStar) :
    conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold d ≤ B ∧
      Real.log (maxFiberSize d : ℝ) / Real.log 2 ≤ B ∧ 0 < rhoPeak - rhoVol := by
  let i0 : Fin n := ⟨0, hn⟩
  have hmax_pos : 0 < maxFiberSize d := by
    exact lt_of_lt_of_le (hd i0) (Finset.le_sup (by simp))
  have hceil :
      Nat.ceil (Real.log (maxFiberSize d : ℝ) / Real.log 2) ≤ B :=
    (paper_conclusion_fold_capacity_wedderburn_exact_bit_threshold
      (maxFiberSize d) B hmax_pos).mp hbudget
  have hthreshold :
      conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold d ≤ B := by
    rw [paper_conclusion_full_inversion_threshold_entropy_gap hn d hd]
    exact hceil
  have hlog_bound : Real.log (maxFiberSize d : ℝ) / Real.log 2 ≤ B := by
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgap_bits :
      Real.log (2 / Real.goldenRatio) / Real.log 2 < alphaStar / Real.log 2 :=
    div_lt_div_of_pos_right hgap hlog2_pos
  refine ⟨hthreshold, hlog_bound, ?_⟩
  rw [hvol, hpeak]
  exact sub_pos.mpr hgap_bits

end Omega.Conclusion
