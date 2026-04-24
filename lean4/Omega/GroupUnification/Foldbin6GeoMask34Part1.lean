import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.GroupUnification

/-- A bit-opposition/equality split for the window-6 geometric `±34` mask identity.
    cor:foldbin6-geo-mask-34-part1 -/
theorem paper_foldbin6_geo_mask_34_part1 (omega : Fin 6 -> Bool) :
    ((omega 0 != omega 4) -> geoStabilizerAction omega = omega) /\
      ((omega 0 = omega 4) ->
        binaryEncode6 (geoStabilizerAction omega) - binaryEncode6 omega = 34 \/
          binaryEncode6 (geoStabilizerAction omega) - binaryEncode6 omega = -34) := by
  constructor
  · intro hneq
    funext i
    fin_cases i
    · cases h0 : omega 0 <;> cases h4 : omega 4 <;>
        simp [geoStabilizerAction, h0, h4] at hneq ⊢
    · simp [geoStabilizerAction]
    · simp [geoStabilizerAction]
    · simp [geoStabilizerAction]
    · cases h0 : omega 0 <;> cases h4 : omega 4 <;>
        simp [geoStabilizerAction, h0, h4] at hneq ⊢
    · simp [geoStabilizerAction]
  · intro heq
    cases h0 : omega 0 <;> cases h4 : omega 4
    · left
      rw [geoStabilizer_mask_34]
      simp [h0, h4]
    · simp [h0, h4] at heq
    · simp [h0, h4] at heq
    · right
      rw [geoStabilizer_mask_34]
      simp [h0, h4]

/-- Paper-facing `0/±34` trichotomy for the window-6 geometric mask, together with the local
    sign rule determined by bits `0` and `4`.
    cor:foldbin6-geo-mask-34 -/
theorem paper_foldbin6_geo_mask_34 (omega : Fin 6 → Bool) :
    let Δ := binaryEncode6 (geoStabilizerAction omega) - binaryEncode6 omega
    (Δ = 0 ∨ Δ = 34 ∨ Δ = -34) ∧
      ((omega 0 != omega 4) ↔ Δ = 0) ∧
      ((omega 0 = omega 4) → (omega 0 = false → Δ = 34) ∧ (omega 0 = true → Δ = -34)) := by
  dsimp
  rcases paper_foldbin6_geo_mask_34_part1 omega with ⟨hneqCase, _⟩
  cases h0 : omega 0 <;> cases h4 : omega 4
  · have hΔ34 :
        binaryEncode6 (geoStabilizerAction omega) - binaryEncode6 omega = 34 := by
      simpa [h0, h4] using paper_geoStabilizer_mask_34 omega
    refine ⟨Or.inr <| Or.inl hΔ34, ?_, ?_⟩
    · constructor
      · intro hneq
        simp [h0, h4] at hneq
      · intro hΔ
        simpa [hΔ34] using hΔ
    · intro heq
      refine ⟨?_, ?_⟩
      · intro _
        exact hΔ34
      · intro htrue
        simp [h0] at htrue
  · have hfix : geoStabilizerAction omega = omega := by
      apply hneqCase
      simp [h0, h4]
    have hΔ0 :
        binaryEncode6 (geoStabilizerAction omega) - binaryEncode6 omega = 0 := by
      simpa [hfix]
    refine ⟨Or.inl hΔ0, ?_, ?_⟩
    · constructor
      · intro _
        exact hΔ0
      · intro _
        simp [h0, h4]
    · intro heq
      simp [h0, h4] at heq
  · have hfix : geoStabilizerAction omega = omega := by
      apply hneqCase
      simp [h0, h4]
    have hΔ0 :
        binaryEncode6 (geoStabilizerAction omega) - binaryEncode6 omega = 0 := by
      simpa [hfix]
    refine ⟨Or.inl hΔ0, ?_, ?_⟩
    · constructor
      · intro _
        exact hΔ0
      · intro _
        simp [h0, h4]
    · intro heq
      simp [h0, h4] at heq
  · have hΔneg34 :
        binaryEncode6 (geoStabilizerAction omega) - binaryEncode6 omega = -34 := by
      simpa [h0, h4] using paper_geoStabilizer_mask_34 omega
    refine ⟨Or.inr <| Or.inr hΔneg34, ?_, ?_⟩
    · constructor
      · intro hneq
        simp [h0, h4] at hneq
      · intro hΔ
        simpa [hΔneg34] using hΔ
    · intro heq
      refine ⟨?_, ?_⟩
      · intro hfalse
        simp [h0] at hfalse
      · intro _
        exact hΔneg34

end Omega.GroupUnification
