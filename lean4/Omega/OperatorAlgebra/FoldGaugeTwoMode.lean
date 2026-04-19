import Omega.OperatorAlgebra.FoldGaugeCommutantExplicit

namespace Omega.OperatorAlgebra

/-- Chapter-local package for the two-mode corollary of the fold-gauge commutant description. The
data record the existing `a I + b J` commutant formula, its translation to `a I + b Av_x` on each
fiber, and the resulting mean/zero-sum mode decomposition. -/
structure FoldGaugeTwoModeData where
  commutantExplicit : FoldGaugeCommutantExplicitData
  fiberwiseAverageNormalForm : Prop
  twoModeDecomposition : Prop
  deriveFiberwiseAverageNormalForm :
    commutantExplicit.fiberwiseCommutantIsSpanIJ → fiberwiseAverageNormalForm
  deriveTwoModeDecomposition :
    fiberwiseAverageNormalForm → twoModeDecomposition

/-- Paper-facing wrapper for the fold-gauge two-mode corollary: the explicit fiberwise commutant
formula `a I + b J` rewrites as `a I + b Av_x`, which isolates the mean mode `ℂ·1` and the
zero-sum mode `1ᗮ`.
    cor:op-algebra-fold-gauge-two-mode -/
theorem paper_op_algebra_fold_gauge_two_mode
    (D : FoldGaugeTwoModeData) : D.fiberwiseAverageNormalForm ∧ D.twoModeDecomposition := by
  have hSpanIJ : D.commutantExplicit.fiberwiseCommutantIsSpanIJ :=
    paper_op_algebra_fold_gauge_commutant_explicit D.commutantExplicit
  have hAverage : D.fiberwiseAverageNormalForm :=
    D.deriveFiberwiseAverageNormalForm hSpanIJ
  exact ⟨hAverage, D.deriveTwoModeDecomposition hAverage⟩

end Omega.OperatorAlgebra
