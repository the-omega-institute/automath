import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`thm:xi-time-part62dcb-zg-density-row-ratio-riccati-product`. -/
theorem paper_xi_time_part62dcb_zg_density_row_ratio_riccati_product
    (matrixChain rowRatioRecurrence eulerProduct densityFormula : Prop)
    (hmatrix : matrixChain) (hrow : matrixChain -> rowRatioRecurrence)
    (hprod : rowRatioRecurrence -> eulerProduct) (hdens : eulerProduct -> densityFormula) :
    rowRatioRecurrence ∧ eulerProduct ∧ densityFormula := by
  have hrow' : rowRatioRecurrence := hrow hmatrix
  have hprod' : eulerProduct := hprod hrow'
  exact ⟨hrow', hprod', hdens hprod'⟩

end Omega.Zeta
