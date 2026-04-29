import Mathlib.Tactic
import Omega.Conclusion.PrimeRegisterStageRamanujanLayerDetection

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-prime-register-stage-ramanujan-shadow-recovers-budget`. -/
theorem paper_conclusion_prime_register_stage_ramanujan_shadow_recovers_budget
    (D : conclusion_prime_register_stage_ramanujan_layer_detection_data) :
    let M := conclusion_prime_register_stage_ramanujan_layer_detection_stage_modulus D
    M = D.stagePrime ^ D.stageDepth ∧
      ∀ r : ℕ, M ^ r = (D.stagePrime ^ D.stageDepth) ^ r := by
  dsimp [conclusion_prime_register_stage_ramanujan_layer_detection_stage_modulus]
  exact ⟨rfl, fun _ => rfl⟩

end Omega.Conclusion
