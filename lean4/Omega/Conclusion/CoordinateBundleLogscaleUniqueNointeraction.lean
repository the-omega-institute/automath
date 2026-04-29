import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-coordinate-bundle-logscale-unique-nointeraction`. -/
theorem paper_conclusion_coordinate_bundle_logscale_unique_nointeraction (n : ℕ)
    (u : ℕ → ℤ) :
    (∀ s : ℕ, s + 2 ≤ n → u (s + 2) - 2 * u (s + 1) + u s = 0) ↔
      ∃ A B : ℤ, ∀ s : ℕ, s ≤ n → u s = A + B * (s : ℤ) := by
  constructor
  · intro hsecond
    refine ⟨u 0, u 1 - u 0, ?_⟩
    intro s hs
    induction s using Nat.strong_induction_on with
    | h s ih =>
        rcases s with _ | s
        · simp
        rcases s with _ | s
        · simp
        have hs0 : s ≤ n := by omega
        have hs1 : s + 1 ≤ n := by omega
        have hs2 : s + 2 ≤ n := by simpa [Nat.succ_eq_add_one] using hs
        have hrec : u (s + 2) = 2 * u (s + 1) - u s := by
          have h := hsecond s hs2
          linarith
        have hih0 : u s = u 0 + (u 1 - u 0) * (s : ℤ) := ih s (by omega) hs0
        have hih1 : u (s + 1) = u 0 + (u 1 - u 0) * ((s + 1 : ℕ) : ℤ) :=
          ih (s + 1) (by omega) hs1
        rw [hrec, hih0, hih1]
        push_cast
        ring
  · rintro ⟨A, B, haffine⟩ s hs
    have hs0 : s ≤ n := by omega
    have hs1 : s + 1 ≤ n := by omega
    have hs2 : s + 2 ≤ n := hs
    rw [haffine (s + 2) hs2, haffine (s + 1) hs1, haffine s hs0]
    push_cast
    ring

end Omega.Conclusion
