namespace Omega.POM

/-- Paper label: `cor:pom-bc-zero-defect-rigidity-parenthesization`. -/
theorem paper_pom_bc_zero_defect_rigidity_parenthesization
    {Index : Type u} {Bracketing : Type v} {Distribution : Type w} (totalDefectZero : Prop)
    (localDefectZero : Index → Prop) (bracketDistribution : Bracketing → Distribution)
    (hzero : totalDefectZero ↔ ∀ i, localDefectZero i)
    (hbracket :
      (∀ i, localDefectZero i) → ∀ b1 b2, bracketDistribution b1 = bracketDistribution b2) :
    totalDefectZero ↔
      (∀ i, localDefectZero i) ∧ ∀ b1 b2, bracketDistribution b1 = bracketDistribution b2 := by
  constructor
  · intro htotal
    have hlocal : ∀ i, localDefectZero i := hzero.mp htotal
    exact ⟨hlocal, hbracket hlocal⟩
  · intro hpackage
    exact hzero.mpr hpackage.1

end Omega.POM
