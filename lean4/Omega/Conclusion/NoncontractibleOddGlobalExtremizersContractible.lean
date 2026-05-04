import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-noncontractible-odd-global-extremizers-contractible`. -/
theorem paper_conclusion_noncontractible_odd_global_extremizers_contractible
    (m : ℕ) (DeltaNc D2 D3 : ℝ) (globalContractible positiveSector : Prop)
    (hglobal : globalContractible) (hpositive : positiveSector)
    (h15 : m % 6 = 1 ∨ m % 6 = 5 → DeltaNc = Real.log D2)
    (h3 : m % 6 = 3 → DeltaNc = Real.log D3) :
    globalContractible ∧ positiveSector ∧
      ((m % 6 = 1 ∨ m % 6 = 5) → DeltaNc = Real.log D2) ∧
        (m % 6 = 3 → DeltaNc = Real.log D3) := by
  exact ⟨hglobal, hpositive, h15, h3⟩

end Omega.Conclusion
