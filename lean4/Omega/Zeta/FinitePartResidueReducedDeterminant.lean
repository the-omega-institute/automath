import Omega.Zeta.AbelFinitePartMobiusZeta
import Omega.Zeta.DynZeta

namespace Omega.Zeta

noncomputable section

/-- Paper label: `prop:finite-part-residue-reduced-determinant`. Separating the simple residue
term gives the finite-part closed form, and the golden-mean reduced determinant is the resulting
specialized value at the Perron pole. -/
theorem paper_finite_part_residue_reduced_determinant
    (D : AbelFinitePartMobiusZetaData) :
    D.finitePartClosedForm ∧
      1 - Real.goldenConj / Real.goldenRatio = Real.sqrt 5 / Real.goldenRatio := by
  exact ⟨paper_etds_abel_finite_part_mobius_zeta D, reduced_det_golden_mean⟩

end

end Omega.Zeta
