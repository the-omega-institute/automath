import Omega.Zeta.FinitePartLogMPrimitiveOrbitClosedForm
import Omega.Zeta.PsiTruncationBounds

namespace Omega.Zeta

/-- Paper-facing package for `cor:finite-part-logM-gap-positive`: the primitive-orbit expansion
records the finite-part gap, and any first primitive-orbit contribution lying in `(0, 1)` yields a
strictly positive `psi` correction. -/
def finite_part_logm_gap_positive_statement (A : PrimitiveOrbitZetaDatum) : Prop :=
  finitePartLogMPrimitiveOrbitClosedForm A ∧
    (0 < A.primitiveOrbitWeight 1 →
      A.primitiveOrbitWeight 1 < 1 →
      0 < PsiTruncationBounds.psi (A.primitiveOrbitWeight 1))

/-- Paper label: `cor:finite-part-logM-gap-positive`. The primitive-orbit closed form packages the
finite-part `log M` gap, and the existing `psi` positivity lemma shows that any nontrivial first
primitive-orbit term contributes a strictly positive amount. -/
theorem paper_finite_part_logm_gap_positive (A : PrimitiveOrbitZetaDatum) :
    finite_part_logm_gap_positive_statement A := by
  refine ⟨paper_finite_part_logM_primitive_orbit_closed_form A, ?_⟩
  intro hpos hlt
  simpa using PsiTruncationBounds.psi_pos (A.primitiveOrbitWeight 1) hpos hlt

end Omega.Zeta
