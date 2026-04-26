import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-mod-readout-external-half-circle-budget`. -/
theorem paper_conclusion_mod_readout_external_half_circle_budget (b : ℕ) (hb : 2 ≤ b) :
    Function.Injective (fun n : ℕ => (n % b, n / b)) := by
  intro m n hmn
  have hb_pos : 0 < b := by omega
  have _hm_lt : m % b < b := Nat.mod_lt _ hb_pos
  have _hn_lt : n % b < b := Nat.mod_lt _ hb_pos
  have hsum :
      m % b + b * (m / b) = n % b + b * (n / b) := by
    simpa using congrArg (fun p : ℕ × ℕ => p.1 + b * p.2) hmn
  simpa [Nat.mod_add_div] using hsum

end Omega.Conclusion
