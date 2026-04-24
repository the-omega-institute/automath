import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete reset-gap data modeled by a periodic reset event of period `maxGap`. -/
structure ZeckendorfResetObservationThresholdData where
  maxGap : ℕ
  two_le_maxGap : 2 ≤ maxGap

namespace ZeckendorfResetObservationThresholdData

/-- Reset events occur exactly at multiples of the maximal gap. -/
def isReset (D : ZeckendorfResetObservationThresholdData) (n : ℕ) : Prop :=
  n % D.maxGap = 0

/-- A scan window avoids resets when no point in it is a reset event. -/
def windowAvoidsReset (D : ZeckendorfResetObservationThresholdData) (start len : ℕ) : Prop :=
  ∀ n, start ≤ n → n < start + len → ¬ D.isReset n

/-- A gap length is admissible if some window of that length avoids resets. -/
def admissibleGap (D : ZeckendorfResetObservationThresholdData) (len : ℕ) : Prop :=
  ∃ start, D.windowAvoidsReset start len

/-- A concrete reset-count model with exact period `maxGap`. -/
def resetCountUpTo (D : ZeckendorfResetObservationThresholdData) (N : ℕ) : ℕ :=
  N / D.maxGap + if N % D.maxGap = 0 then 0 else 1

/-- The largest admissible gap is exactly `maxGap - 1`. -/
def gapSetLaw (D : ZeckendorfResetObservationThresholdData) : Prop :=
  D.admissibleGap (D.maxGap - 1) ∧ ∀ len, D.admissibleGap len → len ≤ D.maxGap - 1

/-- Windows of length `maxGap - 1` can avoid resets, but every window of length `maxGap` hits one. -/
def exactDeterministicThreshold (D : ZeckendorfResetObservationThresholdData) : Prop :=
  (∃ start, D.windowAvoidsReset start (D.maxGap - 1)) ∧
    ∀ start, ∃ n, start ≤ n ∧ n < start + D.maxGap ∧ D.isReset n

/-- The periodic reset count has bounded discrepancy at scale `maxGap`. -/
def densityBound (D : ZeckendorfResetObservationThresholdData) : Prop :=
  ∀ N, D.resetCountUpTo N ≤ N / D.maxGap + 1

private theorem avoid_short_window (D : ZeckendorfResetObservationThresholdData) :
    D.windowAvoidsReset 1 (D.maxGap - 1) := by
  intro n hnLower hnUpper hReset
  have hlt : n < D.maxGap := by
    omega
  have hmod : n % D.maxGap = n := Nat.mod_eq_of_lt hlt
  unfold isReset at hReset
  rw [hmod] at hReset
  omega

private theorem hit_full_window (D : ZeckendorfResetObservationThresholdData) (start : ℕ) :
    ∃ n, start ≤ n ∧ n < start + D.maxGap ∧ D.isReset n := by
  let r := start % D.maxGap
  by_cases hr : r = 0
  · refine ⟨start, le_rfl, ?_, ?_⟩
    · have hgap_pos : 0 < D.maxGap := by
        exact lt_of_lt_of_le (by decide : 0 < 2) D.two_le_maxGap
      exact Nat.lt_add_of_pos_right hgap_pos
    · simpa [isReset, r] using hr
  · have hgap_pos : 0 < D.maxGap := by
      exact lt_of_lt_of_le (by decide : 0 < 2) D.two_le_maxGap
    have hr_lt : r < D.maxGap := by
      simpa [r] using Nat.mod_lt start hgap_pos
    let n := start + (D.maxGap - r)
    refine ⟨n, ?_, ?_, ?_⟩
    · dsimp [n]
      omega
    · dsimp [n]
      omega
    · have hstart : r + D.maxGap * (start / D.maxGap) = start := by
        simpa [r] using Nat.mod_add_div start D.maxGap
      have hdiv : D.maxGap ∣ n := by
        refine ⟨start / D.maxGap + 1, ?_⟩
        dsimp [n]
        calc
          start + (D.maxGap - r)
              = (r + D.maxGap * (start / D.maxGap)) + (D.maxGap - r) := by
                  rw [hstart]
          _ = D.maxGap * (start / D.maxGap) + (r + (D.maxGap - r)) := by ac_rfl
          _ = D.maxGap * (start / D.maxGap) + D.maxGap := by
                rw [Nat.add_sub_of_le (Nat.le_of_lt hr_lt)]
          _ = D.maxGap * (start / D.maxGap + 1) := by ring
      exact Nat.mod_eq_zero_of_dvd hdiv

theorem gap_set_law (D : ZeckendorfResetObservationThresholdData) : D.gapSetLaw := by
  refine ⟨⟨1, avoid_short_window D⟩, ?_⟩
  intro len hLen
  rcases hLen with ⟨start, hAvoid⟩
  by_contra hLarge
  have hGapLe : D.maxGap ≤ len := by omega
  rcases hit_full_window D start with ⟨n, hnLower, hnUpper, hReset⟩
  have hnUpper' : n < start + len := by omega
  exact (hAvoid n hnLower hnUpper' hReset).elim

theorem exact_threshold (D : ZeckendorfResetObservationThresholdData) : D.exactDeterministicThreshold := by
  refine ⟨⟨1, avoid_short_window D⟩, ?_⟩
  intro start
  exact hit_full_window D start

theorem density_bound (D : ZeckendorfResetObservationThresholdData) : D.densityBound := by
  intro N
  unfold resetCountUpTo
  split_ifs <;> omega

end ZeckendorfResetObservationThresholdData

/-- Paper label: `thm:conclusion-zeckendorf-reset-observation-threshold`. -/
theorem paper_conclusion_zeckendorf_reset_observation_threshold
    (D : ZeckendorfResetObservationThresholdData) :
    D.gapSetLaw ∧ D.exactDeterministicThreshold ∧ D.densityBound := by
  exact ⟨D.gap_set_law, D.exact_threshold, D.density_bound⟩

end Omega.Conclusion
