import Mathlib.Tactic
import Omega.SPG.DyadicBoundaryImageLDPC
import Omega.SPG.DyadicBoundaryImageMinDistance

namespace Omega.Conclusion

/-- Concrete dyadic boundary-image code data for the fixed-resolution hologram package. -/
structure FixedResolutionHologramCodeData where
  Cn : Type*
  Cn1 : Type*
  instAddGroupCn : AddGroup Cn
  instAddGroupCn1 : AddGroup Cn1
  boundaryTop : Cn → Cn1
  m : ℕ
  n : ℕ
  hn : 1 ≤ n
  hSub : ∀ u v, boundaryTop (u - v) = boundaryTop u - boundaryTop v
  hKer : ∀ u, boundaryTop u = 0 → u = 0

attribute [instance] FixedResolutionHologramCodeData.instAddGroupCn
attribute [instance] FixedResolutionHologramCodeData.instAddGroupCn1

namespace FixedResolutionHologramCodeData

/-- The exact coding-theoretic package extracted from the dyadic boundary-image LDPC law and the
minimum-distance formula `d_min = 2n`. -/
def exactErrorRadius (D : FixedResolutionHologramCodeData) : Prop :=
  Omega.SPG.dyadicBoundaryImageMinDistance D.m D.n = 2 * D.n ∧
    (Omega.SPG.dyadicBoundaryImageMinDistance D.m D.n - 1) / 2 = D.n - 1 ∧
    Omega.SPG.dyadicBoundaryImageMinDistance D.m D.n - 1 = 2 * D.n - 1 ∧
    Omega.SPG.dyadicBoundaryImageRate D.n D.m = (2 ^ D.m : ℚ) / (D.n * (2 ^ D.m + 1))

end FixedResolutionHologramCodeData

set_option maxHeartbeats 400000 in
/-- The dyadic boundary-image code has exact correction radius `n - 1`, exact detection radius
`2n - 1`, and the closed-form positive rate from the LDPC package.
    cor:conclusion-fixed-resolution-hologram-exact-error-radius -/
theorem paper_conclusion_fixed_resolution_hologram_exact_error_radius
    (D : FixedResolutionHologramCodeData) : D.exactErrorRadius := by
  unfold FixedResolutionHologramCodeData.exactErrorRadius
  have hLDPC :=
    Omega.SPG.paper_spg_dyadic_boundary_image_ldpc D.boundaryTop D.n D.m D.hSub D.hKer
  have hDist := Omega.SPG.paper_spg_dyadic_boundary_image_min_distance D.m D.n D.hn
  refine ⟨hDist, ?_, ?_, ?_⟩
  · omega
  · omega
  · simpa using hLDPC.2.2.1

end Omega.Conclusion
