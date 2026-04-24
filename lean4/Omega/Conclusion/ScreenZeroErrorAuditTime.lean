import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-screen-zeroerror-audit-time`. -/
theorem paper_conclusion_screen_zeroerror_audit_time (A beta : Nat) (hA : 2 <= A) :
    ∃ T : Nat, A ^ T >= 2 ^ beta ∧ ∀ t < T, A ^ t < 2 ^ beta := by
  have hExists : ∃ t : Nat, 2 ^ beta ≤ A ^ t := by
    refine ⟨beta, ?_⟩
    exact Nat.pow_le_pow_left hA beta
  let T : Nat := Nat.find hExists
  refine ⟨T, Nat.find_spec hExists, ?_⟩
  intro t ht
  exact lt_of_not_ge fun hge =>
    (Nat.not_le_of_lt ht) (Nat.find_min' hExists hge)

end Omega.Conclusion
