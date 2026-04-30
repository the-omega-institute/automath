import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-smith-normalized-kernel-dirichlet-torsion-equivalence`. -/
theorem paper_conclusion_smith_normalized_kernel_dirichlet_torsion_equivalence
    {dirichletEq coeffEq localValuationEq torsionCokerIso : Prop}
    (h12 : dirichletEq ↔ coeffEq)
    (h23 : coeffEq ↔ localValuationEq)
    (h34 : localValuationEq ↔ torsionCokerIso) :
    (dirichletEq ↔ coeffEq) ∧ (coeffEq ↔ localValuationEq) ∧
      (localValuationEq ↔ torsionCokerIso) ∧ (dirichletEq ↔ torsionCokerIso) := by
  exact ⟨h12, h23, h34, h12.trans (h23.trans h34)⟩

end Omega.Conclusion
