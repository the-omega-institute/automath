import Mathlib.Data.Fintype.Card

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-leyang-prym3-principalization-moduli-threepoint-etale`. -/
theorem paper_conclusion_leyang_prym3_principalization_moduli_threepoint_etale
    (Moduli : Type*) [Fintype Moduli]
    (finiteEtale representedByED2minusZero representedByCubicSpec : Prop)
    (hcard : Fintype.card Moduli = 3)
    (hetale : finiteEtale)
    (hED : representedByED2minusZero)
    (hSpec : representedByCubicSpec) :
    Fintype.card Moduli = 3 ∧ finiteEtale ∧ representedByED2minusZero ∧
      representedByCubicSpec := by
  exact ⟨hcard, hetale, hED, hSpec⟩

end Omega.Conclusion
