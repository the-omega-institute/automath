import Mathlib.Data.Complex.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-halting-walsh-breakpoint`. -/
theorem paper_conclusion_halting_walsh_breakpoint
    (L N : ℕ) (fourierCoeff : ℕ → ℂ) (halted neverHalts : Prop)
    (hLow : halted → ∀ k : ℕ, k ≤ L * N → fourierCoeff k = 1)
    (hBreak : halted → ∃ k : ℕ, k = L * N + 1 ∧ fourierCoeff k = 0)
    (hNever : neverHalts → ∀ k : ℕ, fourierCoeff k = 1) :
    (halted →
        (∀ k : ℕ, k ≤ L * N → fourierCoeff k = 1) ∧
          ∃ k : ℕ, k = L * N + 1 ∧ fourierCoeff k = 0) ∧
      (neverHalts → ∀ k : ℕ, fourierCoeff k = 1) := by
  refine ⟨?_, ?_⟩
  · intro hhalted
    exact ⟨hLow hhalted, hBreak hhalted⟩
  · intro hnever
    exact hNever hnever

end Omega.Conclusion
