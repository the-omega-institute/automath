import Mathlib.Tactic
import Omega.SPG.DyadicBoundaryImageLDPC
import Omega.SPG.DyadicBoundaryImageMinDistance

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-boundary-image-ldpc-576-64-12`. -/
theorem paper_conclusion_window6_boundary_image_ldpc_576_64_12
    {Cn Cn1 : Type*} [AddGroup Cn] [AddGroup Cn1]
    (boundaryTop : Cn → Cn1)
    (hSub : ∀ u v, boundaryTop (u - v) = boundaryTop u - boundaryTop v)
    (hKer : ∀ u, boundaryTop u = 0 → u = 0) :
    Omega.SPG.dyadicBoundaryImageBlockLength 6 1 = 576 ∧
      Omega.SPG.dyadicBoundaryImageDimension boundaryTop 6 1 = 64 ∧
      Omega.SPG.dyadicBoundaryImageMinDistance 1 6 = 12 ∧
      Omega.SPG.dyadicBoundaryImageRate 6 1 = (1 / 9 : ℚ) ∧
      Omega.SPG.dyadicBoundaryCheckDegree = 4 ∧
      Omega.SPG.dyadicBoundaryVariableDegree 6 = 10 := by
  have hldpc :=
    Omega.SPG.paper_spg_dyadic_boundary_image_ldpc boundaryTop 6 1 hSub hKer
  have hdist := Omega.SPG.paper_spg_dyadic_boundary_image_min_distance 1 6 (by norm_num)
  rcases hldpc with ⟨hblock, hdim, hrate, hcheck, hvar, _hcode⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hblock]
    norm_num
  · rw [hdim]
    norm_num
  · rw [hdist]
  · rw [hrate]
    norm_num
  · exact hcheck
  · rw [hvar]

/-- Paper label: `cor:conclusion-window6-boundary-ldpc-minsupport-12`. -/
theorem paper_conclusion_window6_boundary_ldpc_minsupport_12 :
    Omega.SPG.dyadicBoundaryImageMinDistance 1 6 = 12 := by
  simpa using Omega.SPG.paper_spg_dyadic_boundary_image_min_distance 1 6 (by norm_num)

end Omega.Conclusion
