import Mathlib.Tactic

namespace Omega.Conclusion

theorem paper_conclusion_bivariate_minreal_finitewindow_spectral_surface_rigidity
    (finiteWindowRankClosed minKernelSimilar characteristicDet primitiveEquation spectralSurface
      eliminationCurvesDetermined : Prop)
    (hKernel : finiteWindowRankClosed → minKernelSimilar)
    (hDet : minKernelSimilar → characteristicDet)
    (hPrimitive : characteristicDet → primitiveEquation)
    (hSurface : primitiveEquation → spectralSurface)
    (hElim : primitiveEquation → eliminationCurvesDetermined)
    (hClosed : finiteWindowRankClosed) :
    minKernelSimilar ∧ characteristicDet ∧ primitiveEquation ∧ spectralSurface ∧
      eliminationCurvesDetermined := by
  exact ⟨hKernel hClosed, hDet (hKernel hClosed), hPrimitive (hDet (hKernel hClosed)),
    hSurface (hPrimitive (hDet (hKernel hClosed))),
    hElim (hPrimitive (hDet (hKernel hClosed)))⟩

end Omega.Conclusion
