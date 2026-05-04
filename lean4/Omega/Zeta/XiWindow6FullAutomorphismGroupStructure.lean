import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-window6-full-automorphism-group-structure`. -/
theorem paper_xi_window6_full_automorphism_group_structure
    (AutG Model : Type*) (decode : AutG ≃ Model)
    (centralTwistRank centerRank abelianizedRank : Nat)
    (hrank : centralTwistRank = centerRank * abelianizedRank)
    (hcenter : centerRank = 8) (hab : abelianizedRank = 13) :
    Nonempty (AutG ≃ Model) ∧ centralTwistRank = 104 := by
  refine ⟨⟨decode⟩, ?_⟩
  calc
    centralTwistRank = centerRank * abelianizedRank := hrank
    _ = 8 * 13 := by rw [hcenter, hab]
    _ = 104 := by norm_num

end Omega.Zeta
