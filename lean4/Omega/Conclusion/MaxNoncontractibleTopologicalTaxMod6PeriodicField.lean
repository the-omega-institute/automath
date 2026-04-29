import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-max-noncontractible-topological-tax-mod6-periodic-field`. -/
theorem paper_conclusion_max_noncontractible_topological_tax_mod6_periodic_field
    (TopologicalTax : Nat -> Prop) (MeanLocked ZeroTaxDensityOneThird : Prop)
    (hperiodic : forall m, 17 <= m -> TopologicalTax m) (hmean : MeanLocked)
    (hdensity : ZeroTaxDensityOneThird) :
    (forall m, 17 <= m -> TopologicalTax m) ∧ MeanLocked ∧ ZeroTaxDensityOneThird := by
  exact ⟨hperiodic, hmean, hdensity⟩

end Omega.Conclusion
