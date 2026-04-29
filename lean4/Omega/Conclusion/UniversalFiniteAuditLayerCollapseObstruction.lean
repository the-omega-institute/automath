import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-universal-finite-audit-layer-collapse-obstruction`. -/
theorem paper_conclusion_universal_finite_audit_layer_collapse_obstruction
    (UniversalFiniteAuditLayer P_eq_NP : Prop)
    (hcollapse : UniversalFiniteAuditLayer → P_eq_NP) :
    ¬ P_eq_NP → ¬ UniversalFiniteAuditLayer := by
  intro hnot_eq hlayer
  exact hnot_eq (hcollapse hlayer)

end Omega.Conclusion
