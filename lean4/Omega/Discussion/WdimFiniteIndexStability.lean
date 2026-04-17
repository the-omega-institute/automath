import Omega.CircleDimension.SignedCircleDimension
import Omega.CircleDimension.WdimSignedCircleDimension

namespace Omega.Discussion

open Omega.CircleDimension

/-- Finite-index stability of the weighted dimension in the bookkeeping model: finite extensions
preserve the free ranks, hence preserve the signed circle dimension, and the bridge
`wdim = cdimSigned` transfers that invariance to `wdim`.
    cor:discussion-wdim-finite-index-stability -/
  theorem paper_discussion_wdim_finite_index_stability
      (u₁ v₁ tu₁ tq₁ u₂ v₂ tu₂ tq₂ : ℕ) (hu : u₁ = u₂) (hv : v₁ = v₂) :
      wdim (u₁ : ℚ) (v₁ : ℚ) = wdim (u₂ : ℚ) (v₂ : ℚ) := by
  have hSigned : cdimSigned u₁ v₁ tu₁ tq₁ = cdimSigned u₂ v₂ tu₂ tq₂ :=
    (paper_cdim_signed_laws.2.2.2 u₁ v₁ tu₁ tq₁ u₂ v₂ tu₂ tq₂) hu hv
  have hBridge₁ : wdim (u₁ : ℚ) (v₁ : ℚ) = cdimSigned u₁ v₁ 0 0 :=
    paper_cdim_stokes_character_contraction_general_monoid u₁ v₁
  have hBridge₂ : wdim (u₂ : ℚ) (v₂ : ℚ) = cdimSigned u₂ v₂ 0 0 :=
    paper_cdim_stokes_character_contraction_general_monoid u₂ v₂
  calc
    wdim (u₁ : ℚ) (v₁ : ℚ) = cdimSigned u₁ v₁ 0 0 := hBridge₁
    _ = cdimSigned u₁ v₁ tu₁ tq₁ := by
      simp [cdimSigned, circleDim, halfCircleDim]
    _ = cdimSigned u₂ v₂ tu₂ tq₂ := hSigned
    _ = cdimSigned u₂ v₂ 0 0 := by
      simp [cdimSigned, circleDim, halfCircleDim]
    _ = wdim (u₂ : ℚ) (v₂ : ℚ) := hBridge₂.symm

end Omega.Discussion
