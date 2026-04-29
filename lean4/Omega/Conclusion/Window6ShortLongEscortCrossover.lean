import Mathlib.Tactic

namespace Omega.Conclusion

/-- Window-`6` escort denominator from the histogram `2:8, 3:4, 4:9`. -/
def conclusion_window6_short_long_escort_crossover_denominator (q : ℕ) : ℕ :=
  9 * 4 ^ q + 4 * 3 ^ q + 8 * 2 ^ q

/-- Short-root numerator: one degree-`2` point and five degree-`4` points. -/
def conclusion_window6_short_long_escort_crossover_shortNumerator (q : ℕ) : ℕ :=
  5 * 4 ^ q + 2 ^ q

/-- Long-root numerator: four points in each of degrees `2`, `3`, and `4`. -/
def conclusion_window6_short_long_escort_crossover_longNumerator (q : ℕ) : ℕ :=
  4 * 4 ^ q + 4 * 3 ^ q + 4 * 2 ^ q

/-- Boundary numerator: three degree-`2` boundary points. -/
def conclusion_window6_short_long_escort_crossover_boundaryNumerator (q : ℕ) : ℕ :=
  3 * 2 ^ q

/-- The integer numerator of the short-minus-long escort mass difference. -/
def conclusion_window6_short_long_escort_crossover_signedNumerator (q : ℕ) : ℤ :=
  (4 : ℤ) ^ q - 4 * (3 : ℤ) ^ q - 3 * (2 : ℤ) ^ q

/-- Concrete finite-power form of the window-`6` short/long escort crossover. -/
def conclusion_window6_short_long_escort_crossover_statement : Prop :=
  (∀ q : ℕ,
      conclusion_window6_short_long_escort_crossover_denominator q =
        conclusion_window6_short_long_escort_crossover_shortNumerator q +
          conclusion_window6_short_long_escort_crossover_longNumerator q +
            conclusion_window6_short_long_escort_crossover_boundaryNumerator q) ∧
    conclusion_window6_short_long_escort_crossover_signedNumerator 5 < 0 ∧
      0 < conclusion_window6_short_long_escort_crossover_signedNumerator 6 ∧
        (∀ q : ℕ, q ≤ 5 →
          conclusion_window6_short_long_escort_crossover_signedNumerator q < 0) ∧
          (∀ q : ℕ, 6 ≤ q →
            0 < conclusion_window6_short_long_escort_crossover_signedNumerator q)

lemma conclusion_window6_short_long_escort_crossover_signedNumerator_step (q : ℕ) :
    conclusion_window6_short_long_escort_crossover_signedNumerator (q + 1) =
      3 * conclusion_window6_short_long_escort_crossover_signedNumerator q +
        (4 : ℤ) ^ q + 3 * (2 : ℤ) ^ q := by
  unfold conclusion_window6_short_long_escort_crossover_signedNumerator
  ring

lemma conclusion_window6_short_long_escort_crossover_signedNumerator_pos_from_six
    (q : ℕ) (hq : 6 ≤ q) :
    0 < conclusion_window6_short_long_escort_crossover_signedNumerator q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  induction n with
  | zero =>
      norm_num [conclusion_window6_short_long_escort_crossover_signedNumerator]
  | succ n ih =>
      rw [Nat.add_succ, conclusion_window6_short_long_escort_crossover_signedNumerator_step]
      have ihpos : 0 < conclusion_window6_short_long_escort_crossover_signedNumerator (6 + n) :=
        ih (by omega)
      have hpow4 : 0 < (4 : ℤ) ^ (6 + n) := pow_pos (by norm_num) _
      have hpow2 : 0 < (2 : ℤ) ^ (6 + n) := pow_pos (by norm_num) _
      nlinarith

/-- Paper label: `thm:conclusion-window6-short-long-escort-crossover`. -/
theorem paper_conclusion_window6_short_long_escort_crossover :
    conclusion_window6_short_long_escort_crossover_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q
    unfold conclusion_window6_short_long_escort_crossover_denominator
      conclusion_window6_short_long_escort_crossover_shortNumerator
      conclusion_window6_short_long_escort_crossover_longNumerator
      conclusion_window6_short_long_escort_crossover_boundaryNumerator
    ring
  · norm_num [conclusion_window6_short_long_escort_crossover_signedNumerator]
  · norm_num [conclusion_window6_short_long_escort_crossover_signedNumerator]
  · intro q hq
    interval_cases q <;>
      norm_num [conclusion_window6_short_long_escort_crossover_signedNumerator]
  · exact conclusion_window6_short_long_escort_crossover_signedNumerator_pos_from_six

end Omega.Conclusion
