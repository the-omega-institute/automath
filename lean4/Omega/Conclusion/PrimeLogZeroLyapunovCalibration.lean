import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-prime-log-zero-lyapunov-calibration`. -/
theorem paper_conclusion_prime_log_zero_lyapunov_calibration (c : ℕ) (w : ℕ → ℕ)
    (hw0 : c ≤ w 1) (hmono : ∀ j, w (j + 1) ≤ w (j + 2)) :
    ∃ y δ : ℕ → ℕ, δ 0 = 0 ∧
      (∀ j, (y (j + 1) = 0 ∧ δ j + c ≤ w (j + 1) ∧ δ (j + 1) = δ j + c) ∨
        (y (j + 1) = 1 ∧ w (j + 1) < δ j + c ∧
          δ (j + 1) = δ j + c - w (j + 1))) ∧
      ∀ j, δ j ≤ w (j + 1) := by
  let δ : ℕ → ℕ :=
    Nat.rec 0 fun j dj => if dj + c ≤ w (j + 1) then dj + c else dj + c - w (j + 1)
  let y : ℕ → ℕ := fun n =>
    match n with
    | 0 => 0
    | j + 1 => if δ j + c ≤ w (j + 1) then 0 else 1
  have hw_from_one : ∀ j, w 1 ≤ w (j + 1) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        exact le_trans ih (hmono j)
  have hδ_bound : ∀ j, δ j ≤ w (j + 1) := by
    intro j
    induction j with
    | zero =>
        simp [δ]
    | succ j ih =>
        dsimp [δ]
        by_cases hfit : δ j + c ≤ w (j + 1)
        · exact le_trans (by simp [δ, hfit]) (hmono j)
        · have hle_c : δ j + c - w (j + 1) ≤ c := by
            omega
          exact le_trans (by simp [δ, hfit, hle_c]) (le_trans hw0 (hw_from_one (j + 1)))
  refine ⟨y, δ, ?_, ?_, hδ_bound⟩
  · simp [δ]
  · intro j
    by_cases hfit : δ j + c ≤ w (j + 1)
    · left
      refine ⟨?_, hfit, ?_⟩
      · simp [y, hfit]
      · simp [δ, hfit]
    · right
      refine ⟨?_, Nat.lt_of_not_ge hfit, ?_⟩
      · simp [y, hfit]
      · simp [δ, hfit]

/-- Paper label: `thm:conclusion-prime-log-calibration-zero-lyapunov-product`. -/
theorem paper_conclusion_prime_log_calibration_zero_lyapunov_product (c : ℝ)
    (w δ S logM : ℕ → ℝ) (hc : 0 < c)
    (hw : ∀ j, 1 ≤ j → c < w j ∧ w j < w (j + 1)) (hδ0 : δ 0 = 0)
    (hstep : ∀ j, 1 ≤ j →
      ((δ (j - 1) + c < w j ∧ δ j = δ (j - 1) + c) ∨
        (w j ≤ δ (j - 1) + c ∧ δ j = δ (j - 1) + c - w j)))
    (hS : ∀ j, 1 ≤ j → δ j = c * (j : ℝ) - S j)
    (hlogM : ∀ j, 1 ≤ j → logM j = S j - c * (j : ℝ)) :
    (∀ j, 1 ≤ j → 0 ≤ δ j ∧ δ j < w j) ∧
      (∀ j : ℕ, 1 ≤ j →
        c * (j : ℝ) - w (j + 1) < S j ∧ S j ≤ c * (j : ℝ)) ∧
        (∀ j : ℕ, 1 ≤ j → -w (j + 1) < logM j ∧ logM j ≤ 0) := by
  have hδ_succ : ∀ k, 0 ≤ δ (k + 1) ∧ δ (k + 1) < w (k + 1) := by
    intro k
    induction k with
    | zero =>
        have hw1 : c < w 1 := (hw 1 (by norm_num)).1
        rcases hstep 1 (by norm_num) with hfit | hover
        · rcases hfit with ⟨_, hδ1⟩
          have hδ1' : δ 1 = c := by
            simpa [hδ0] using hδ1
          constructor
          · rw [hδ1']
            linarith
          · rw [hδ1']
            exact hw1
        · rcases hover with ⟨hle, _⟩
          have hle' : w 1 ≤ c := by
            simpa [hδ0] using hle
          linarith
    | succ k ih =>
        have hk1 : 1 ≤ k + 1 := by omega
        have hk2 : 1 ≤ k + 2 := by omega
        have hmono : w (k + 1) < w (k + 2) := (hw (k + 1) hk1).2
        have hc_next : c < w (k + 2) := (hw (k + 2) hk2).1
        rcases hstep (k + 2) hk2 with hfit | hover
        · rcases hfit with ⟨hupper, hδnext⟩
          have hsub : k + 2 - 1 = k + 1 := by omega
          have hupper' : δ (k + 1) + c < w (k + 2) := by
            simpa [hsub] using hupper
          have hδnext' : δ (k + 2) = δ (k + 1) + c := by
            simpa [hsub] using hδnext
          constructor
          · rw [hδnext']
            linarith
          · rw [hδnext']
            exact hupper'
        · rcases hover with ⟨hle, hδnext⟩
          have hsub : k + 2 - 1 = k + 1 := by omega
          have hle' : w (k + 2) ≤ δ (k + 1) + c := by
            simpa [hsub] using hle
          have hδnext' : δ (k + 2) = δ (k + 1) + c - w (k + 2) := by
            simpa [hsub] using hδnext
          have hprev_lt_next : δ (k + 1) < w (k + 2) := by
            linarith
          constructor
          · rw [hδnext']
            linarith
          · rw [hδnext']
            linarith
  have hδ_bound : ∀ j, 1 ≤ j → 0 ≤ δ j ∧ δ j < w j := by
    intro j hj
    cases j with
    | zero => omega
    | succ k => exact hδ_succ k
  have hS_bound :
      ∀ j : ℕ, 1 ≤ j →
        c * (j : ℝ) - w (j + 1) < S j ∧ S j ≤ c * (j : ℝ) := by
    intro j hj
    have hδj := hδ_bound j hj
    have hSj := hS j hj
    have hwmono : w j < w (j + 1) := (hw j hj).2
    constructor
    · linarith
    · linarith
  refine ⟨hδ_bound, hS_bound, ?_⟩
  intro j hj
  have hSj := hS_bound j hj
  have hlogMj := hlogM j hj
  constructor <;> linarith

end Omega.Conclusion
