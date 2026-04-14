import Mathlib.Tactic

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for injective refinements restoring the
    microscopic collision profile in the double-budget section.
    thm:collision-profile-restoration -/
theorem paper_scan_projection_address_collision_profile_restoration
    {Dist Scale : Type}
    (moment : Dist → ℕ → ℝ)
    (collisionStat : Dist → ℝ)
    (birthdayScale : Dist → Scale)
    (collisionTransform : ℝ → ℝ)
    (birthdayTransform : ℝ → Scale)
    (injectiveOnSupport : Prop)
    (hiddenRegisterCost hiddenConditionalEntropy : ℝ)
    {U Y Z : Dist}
    (hcoarse : ∀ r : ℕ, 1 ≤ r → moment Y r ≥ moment U r)
    (heq : ∀ r : ℕ, 1 < r → (moment Y r = moment U r ↔ injectiveOnSupport))
    (hrefined : ∀ r : ℕ, 1 ≤ r → moment Z r = moment U r)
    (hcollisionZ : collisionStat Z = collisionTransform (moment Z 2))
    (hcollisionU : collisionStat U = collisionTransform (moment U 2))
    (hbirthdayZ : birthdayScale Z = birthdayTransform (moment Z 2))
    (hbirthdayU : birthdayScale U = birthdayTransform (moment U 2))
    (hhidden : hiddenRegisterCost = hiddenConditionalEntropy) :
    (∀ r : ℕ, 1 ≤ r → moment Y r ≥ moment U r) ∧
      (∀ r : ℕ, 1 < r → (moment Y r = moment U r ↔ injectiveOnSupport)) ∧
      (∀ r : ℕ, 1 ≤ r → moment Z r = moment U r) ∧
      moment Z 2 = moment U 2 ∧
      collisionStat Z = collisionStat U ∧
      birthdayScale Z = birthdayScale U ∧
      hiddenRegisterCost = hiddenConditionalEntropy := by
  have hmoment2 : moment Z 2 = moment U 2 := hrefined 2 (by norm_num)
  refine ⟨hcoarse, heq, hrefined, hmoment2, ?_, ?_, hhidden⟩
  · rw [hcollisionZ, hcollisionU, hmoment2]
  · rw [hbirthdayZ, hbirthdayU, hmoment2]

end Omega.SPG
