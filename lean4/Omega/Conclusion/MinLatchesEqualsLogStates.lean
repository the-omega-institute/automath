import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-min-latches-equals-log-states`. -/
theorem paper_conclusion_min_latches_equals_log_states (s m : ℕ) (hLower : s ≤ 2 ^ m)
    (hLeast : ∀ k, s ≤ 2 ^ k → m ≤ k) :
    m = Nat.find (⟨m, hLower⟩ : ∃ k : ℕ, s ≤ 2 ^ k) := by
  let witness : ∃ k : ℕ, s ≤ 2 ^ k := ⟨m, hLower⟩
  have hfind : s ≤ 2 ^ Nat.find witness := Nat.find_spec witness
  have hle : m ≤ Nat.find witness := hLeast (Nat.find witness) hfind
  have hge : Nat.find witness ≤ m := Nat.find_min' witness hLower
  exact Nat.le_antisymm hle hge

end Omega.Conclusion
