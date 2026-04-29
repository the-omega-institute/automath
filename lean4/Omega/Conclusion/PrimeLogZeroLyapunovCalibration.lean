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

end Omega.Conclusion
