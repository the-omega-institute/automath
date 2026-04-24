import Mathlib.Tactic
import Omega.Conclusion.Window6Collision
import Omega.Conclusion.Window6FirstThreeMomentsRecoverWedderburnType

namespace Omega.Conclusion

/-- The audited window-`6` Wedderburn histogram. -/
def window6SemisimpleHistogram (d : ℕ) : ℕ :=
  if d = 2 then 8 else if d = 3 then 4 else if d = 4 then 9 else 0

/-- The audited integer-threshold capacity curve attached to the window-`6` histogram. -/
def window6CapacityCurve (t : ℕ) : ℕ :=
  8 * min 2 t + 4 * min 3 t + 9 * min 4 t

/-- Tail-difference reconstruction of the multiplicity histogram from the capacity curve. -/
def window6HistogramFromCapacity (C : ℕ → ℕ) (d : ℕ) : ℕ :=
  (C d - C (d - 1)) - (C (d + 1) - C d)

/-- The window-`6` histogram is recovered from the audited capacity curve, the first three moments
match the existing conclusion data, and any histogram-valued semisimple invariant factors through
the capacity curve by precomposing with this reconstruction map. -/
def Window6SemisimpleInvariantsFactorThroughCapacity (m : Nat) : Prop :=
  1 ≤ m ∧
    (∀ d, window6HistogramFromCapacity window6CapacityCurve d = window6SemisimpleHistogram d) ∧
    (8 + 4 + 9 = 21 ∧ 8 * 2 + 4 * 3 + 9 * 4 = 64 ∧ 8 * 4 + 4 * 9 + 9 * 16 = 212) ∧
    (8 = 8 ∧ 4 = 4 ∧ 9 = 9) ∧
    (∀ {β : Type*} (Obs : (ℕ → ℕ) → β),
      ∃ Φ : (ℕ → ℕ) → β,
        Φ window6CapacityCurve = Obs window6SemisimpleHistogram ∧
          ∀ C, Φ C = Obs (window6HistogramFromCapacity C))

private theorem window6HistogramFromCapacity_eq (d : ℕ) :
    window6HistogramFromCapacity window6CapacityCurve d = window6SemisimpleHistogram d := by
  rcases lt_or_ge d 5 with hd | hd
  · interval_cases d <;> native_decide
  · have hCd : window6CapacityCurve d = 64 := by
      unfold window6CapacityCurve
      norm_num [Nat.min_eq_left (by omega : 2 ≤ d), Nat.min_eq_left (by omega : 3 ≤ d),
        Nat.min_eq_left (by omega : 4 ≤ d)]
    have hCdPred : window6CapacityCurve (d - 1) = 64 := by
      unfold window6CapacityCurve
      norm_num [Nat.min_eq_left (by omega : 2 ≤ d - 1), Nat.min_eq_left (by omega : 3 ≤ d - 1),
        Nat.min_eq_left (by omega : 4 ≤ d - 1)]
    have hCdSucc : window6CapacityCurve (d + 1) = 64 := by
      unfold window6CapacityCurve
      norm_num [Nat.min_eq_left (by omega : 2 ≤ d + 1), Nat.min_eq_left (by omega : 3 ≤ d + 1),
        Nat.min_eq_left (by omega : 4 ≤ d + 1)]
    have hd2 : d ≠ 2 := by omega
    have hd3 : d ≠ 3 := by omega
    have hd4 : d ≠ 4 := by omega
    rw [window6HistogramFromCapacity, hCd, hCdPred, hCdSucc]
    simp [window6SemisimpleHistogram, hd2, hd3, hd4]

/-- Paper label: `thm:conclusion-window6-semisimple-invariants-factor-through-capacity`. -/
theorem paper_conclusion_window6_semisimple_invariants_factor_through_capacity
    (m : Nat) (hm : 1 <= m) : Window6SemisimpleInvariantsFactorThroughCapacity m := by
  have hq := window6_qmoment_triple
  have hw :=
    paper_conclusion_window6_first_three_moments_recover_wedderburn_type
      hq.1 hq.2.1 hq.2.2
  refine ⟨hm, window6HistogramFromCapacity_eq, hq, hw, ?_⟩
  intro β Obs
  refine ⟨fun C => Obs (window6HistogramFromCapacity C), ?_, ?_⟩
  · have hfun : window6HistogramFromCapacity window6CapacityCurve = window6SemisimpleHistogram :=
      funext window6HistogramFromCapacity_eq
    simp [hfun]
  · intro C
    rfl

end Omega.Conclusion
