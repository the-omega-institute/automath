import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.SyncKernelRealInput.RealInput40MertensTwoSeriesTail
import Omega.SyncKernelRealInput.RealInput40ResidueConstant
import Omega.SyncKernelRealInput.RealInput40VertSingleSeries

namespace Omega.SyncKernelRealInput

/-- Paper label: `cor:real-input-40-logM-fast-prime`.

The real-input-`40` finite-part split gives the logarithmic decomposition
`log M_M = log M_in + p_vert(z_*)`, the evaluation point is the Perron pole
`z_* = λ⁻¹ = 2 - φ`, the residue constant is available in closed form, and the appendix tail
bound provides the fast geometric convergence estimate used in the three-point formula. -/
theorem paper_real_input_40_logm_fast_prime
    (D : Omega.SyncKernelWeighted.RealInput40LogMSplitData) (N : ℕ) :
    Omega.POM.realInput40DetFactorization ∧
      D.logMM = D.logMIn + D.pVertAtPole ∧
      triv_factor_primitive_polynomial_ptriv =
        -((Polynomial.X : Polynomial ℤ)) + Polynomial.C 3 * (Polynomial.X : Polynomial ℤ) ^ 2 ∧
      real_input_40_residue_constant_z_star = real_input_40_residue_constant_lambda⁻¹ ∧
      real_input_40_residue_constant_z_star = 2 - Real.goldenRatio ∧
      real_input_40_residue_constant_value = (47 + 21 * Real.sqrt 5) / 100 ∧
      real_input_40_mertens_two_series_tail_statement N := by
  rcases paper_real_input_40_vert_single_series D N with ⟨hfact, hsplit, htriv, htail⟩
  exact ⟨hfact, hsplit, htriv, rfl,
    real_input_40_residue_constant_z_star_eq_two_sub_phi,
    paper_real_input_40_residue_constant.1,
    by simpa [real_input_40_mertens_two_series_tail_statement] using htail⟩

end Omega.SyncKernelRealInput
