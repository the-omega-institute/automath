import Mathlib.Algebra.Polynomial.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.POM.RealInput40ZetaFactorization
import Omega.SyncKernelRealInput.TrivFactorPrimitivePolynomial
import Omega.SyncKernelWeighted.RealInput40LogMTruncBound
import Omega.SyncKernelWeighted.RealInput40LogMSplit

namespace Omega.SyncKernelRealInput

open Polynomial

/-- Paper label: `cor:real-input-40-vert-single-series`.  The determinant factorization isolates
the vertical part, the trivial short-period factors collapse to the explicit polynomial
`-z + 3 z^2`, and the remaining vertical contribution is the single Möbius-log series already
packaged by the finite-part split. -/
theorem paper_real_input_40_vert_single_series
    (D : Omega.SyncKernelWeighted.RealInput40LogMSplitData) (N : ℕ) :
    Omega.POM.realInput40DetFactorization ∧
      D.logMM = D.logMIn + D.pVertAtPole ∧
      triv_factor_primitive_polynomial_ptriv =
        -((Polynomial.X : Polynomial ℤ)) + Polynomial.C 3 * (Polynomial.X : Polynomial ℤ) ^ 2 ∧
      (∀ n, Omega.SyncKernelWeighted.realInput40LogMTruncTerm 5
          (Real.goldenRatio ^ (2 : ℕ)) N n ≤
            Omega.SyncKernelWeighted.realInput40LogMTruncMajorant 5
              (Real.goldenRatio ^ (2 : ℕ)) N n) ∧
      (∑' n, Omega.SyncKernelWeighted.realInput40LogMTruncTerm 5
          (Real.goldenRatio ^ (2 : ℕ)) N n) ≤
        Omega.SyncKernelWeighted.realInput40LogMTruncGeomBound 5
          (Real.goldenRatio ^ (2 : ℕ)) N ∧
      Omega.SyncKernelWeighted.realInput40LogMTruncGeomBound 5
          (Real.goldenRatio ^ (2 : ℕ)) N =
        Omega.SyncKernelWeighted.realInput40LogMTruncClosedBound 5
          (Real.goldenRatio ^ (2 : ℕ)) N := by
  rcases Omega.POM.paper_pom_zeta_factorization_40 with ⟨hfact, _hzeta, _hshort⟩
  have hA : (0 : ℝ) ≤ 5 := by norm_num
  have hlam : 1 < Real.goldenRatio ^ (2 : ℕ) := by
    nlinarith [Real.one_lt_goldenRatio]
  have htail :=
    Omega.SyncKernelWeighted.paper_real_input_40_logM_trunc_bound 5
      (Real.goldenRatio ^ (2 : ℕ)) N hA hlam
  exact ⟨hfact, Omega.SyncKernelWeighted.paper_real_input_40_logM_split D,
    by simpa using paper_triv_factor_primitive_polynomial.1, htail⟩

end Omega.SyncKernelRealInput
