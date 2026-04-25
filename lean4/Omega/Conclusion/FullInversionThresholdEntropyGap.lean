import Mathlib.Tactic
import Omega.Conclusion.FoldCapacityWedderburnExactBitThreshold
import Omega.Conclusion.MaxentropyGapEqualsLogMaxfiber

namespace Omega.Conclusion

/-- The exact full-inversion threshold read from the largest visible fiber. -/
noncomputable def conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold
    {n : ℕ} (d : Fin n → ℕ) : ℕ :=
  Nat.find <| show ∃ B, maxFiberSize d ≤ 2 ^ B from
    ⟨Nat.clog 2 (maxFiberSize d), Nat.le_pow_clog (by decide : 1 < 2) (maxFiberSize d)⟩

/-- The corresponding maximal entropy gap. -/
noncomputable def conclusion_full_inversion_threshold_entropy_gap_entropyGap
    {n : ℕ} (d : Fin n → ℕ) : ℝ :=
  Real.log (maxFiberSize d : ℝ)

private theorem conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold_spec
    {n : ℕ} (d : Fin n → ℕ) :
    maxFiberSize d ≤ 2 ^ conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold d :=
  Nat.find_spec <| show ∃ B, maxFiberSize d ≤ 2 ^ B from
    ⟨Nat.clog 2 (maxFiberSize d), Nat.le_pow_clog (by decide : 1 < 2) (maxFiberSize d)⟩

private theorem conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold_min
    {n : ℕ} (d : Fin n → ℕ) {B : ℕ} (hB : maxFiberSize d ≤ 2 ^ B) :
    conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold d ≤ B :=
  Nat.find_min' (H := by
    exact ⟨Nat.clog 2 (maxFiberSize d), Nat.le_pow_clog (by decide : 1 < 2) (maxFiberSize d)⟩)
    hB

/-- Paper label: `cor:conclusion-full-inversion-threshold-entropy-gap`.
The exact full-inversion budget is the binary ceiling of the maximal entropy gap. -/
theorem paper_conclusion_full_inversion_threshold_entropy_gap :
    ∀ {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i),
      conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold d =
        Nat.ceil (conclusion_full_inversion_threshold_entropy_gap_entropyGap d / Real.log 2) := by
  intro n hn d hd
  rcases paper_conclusion_maxentropy_gap_equals_log_maxfiber hn d hd with ⟨_, ⟨i, hi, _⟩⟩
  have hmax_pos : 0 < maxFiberSize d := by
    rw [← hi]
    exact hd i
  have hupper :
      Nat.ceil (conclusion_full_inversion_threshold_entropy_gap_entropyGap d / Real.log 2) ≤
        conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold d := by
    have hthreshold :=
      paper_conclusion_fold_capacity_wedderburn_exact_bit_threshold
        (maxFiberSize d)
        (conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold d)
        hmax_pos
    exact hthreshold.mp
      (conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold_spec d)
  have hlower :
      conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold d ≤
        Nat.ceil (conclusion_full_inversion_threshold_entropy_gap_entropyGap d / Real.log 2) := by
    have hthreshold :=
      paper_conclusion_fold_capacity_wedderburn_exact_bit_threshold
        (maxFiberSize d)
        (Nat.ceil (conclusion_full_inversion_threshold_entropy_gap_entropyGap d / Real.log 2))
        hmax_pos
    have hbound :
        maxFiberSize d ≤
          2 ^ Nat.ceil (conclusion_full_inversion_threshold_entropy_gap_entropyGap d / Real.log 2) :=
      hthreshold.mpr le_rfl
    exact conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold_min d hbound
  exact le_antisymm hlower hupper

end Omega.Conclusion
