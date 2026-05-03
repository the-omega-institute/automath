import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-prime-adjunction-finite-depth-inverse-limit-budget-phase`. -/
theorem paper_conclusion_prime_adjunction_finite_depth_inverse_limit_budget_phase
    (b : ℕ → ℕ)
    (hLower : ∀ N, 1 ≤ N → N ≤ b N)
    (hUpper : ∀ N, 1 ≤ N → b N ≤ N)
    (countableShiftRealization : Prop)
    (hShift : countableShiftRealization) :
    (∀ N, 1 ≤ N → b N = N) ∧
      (∀ K, ∃ N, 1 ≤ N ∧ K < b N) ∧
        countableShiftRealization := by
  constructor
  · intro N hN
    exact Nat.le_antisymm (hUpper N hN) (hLower N hN)
  constructor
  · intro K
    refine ⟨K + 1, Nat.succ_pos K, ?_⟩
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self K) (hLower (K + 1) (Nat.succ_pos K))
  · exact hShift

end Omega.Conclusion
