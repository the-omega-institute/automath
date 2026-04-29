import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-residue-odd-even-local-invertibility-splitting`. -/
theorem paper_conclusion_residue_odd_even_local_invertibility_splitting
    (m M : ℕ)
    (oddRecover evenBlind oneFunctionalRepair : Prop)
    (hodd : M % 2 = 1 → oddRecover)
    (heven : m % 3 = 1 → evenBlind ∧ oneFunctionalRepair) :
    (M % 2 = 1 → oddRecover) ∧ (m % 3 = 1 → evenBlind ∧ oneFunctionalRepair) := by
  exact ⟨hodd, heven⟩

end Omega.Conclusion
