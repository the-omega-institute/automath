import Omega.Folding.KilloZGDirichletMatrixEuler
import Omega.Zeta.DerivedZGNoScalarEulerProduct
import Omega.Zeta.XiZGAbelResidueLogDensity

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62dgc-zg-matrix-euler-no-scalar-product`. -/
theorem paper_xi_time_part62dgc_zg_matrix_euler_no_scalar_product
    (W : Omega.Zeta.XiZGAbelResidueLogDensityWitness) :
    ((∀ n, Omega.Folding.zgStateA (n + 1) = Omega.Folding.zgStateA n + Omega.Folding.zgStateB n) ∧
      (∀ n, Omega.Folding.zgStateB (n + 1) = (1 / 2 : ℚ) * Omega.Folding.zgStateB n) ∧
      (∀ n, Omega.Folding.zgDirichletEulerPartial n = 2 - (1 / 2 : ℚ) ^ (n + 1)) ∧
      (∀ n, |Omega.Folding.zgDirichletEulerPartial n - 2| = (1 / 2 : ℚ) ^ (n + 1))) ∧
      W.analytic.residueAtOne = W.analytic.deltaZG ∧
      0 < W.analytic.deltaZG ∧ Omega.Zeta.derivedZGNoScalarEulerProduct := by
  refine ⟨Omega.Folding.paper_killo_zg_dirichlet_matrix_euler, W.analytic.residue_eq_delta,
    W.density_pos, ?_⟩
  exact paper_derived_zg_no_scalar_euler_product

end Omega.Zeta
