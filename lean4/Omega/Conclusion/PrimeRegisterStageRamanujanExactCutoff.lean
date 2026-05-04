import Mathlib.Tactic
import Omega.Conclusion.PrimeRegisterStageRamanujanLayerDetection

namespace Omega.Conclusion

open Omega.Zeta

/-- Paper label: `thm:conclusion-prime-register-stage-ramanujan-exact-cutoff`. For the
singleton stage detector, the prefix determines the stage depth exactly iff it includes the
first zero immediately after the detected plateau. -/
theorem paper_conclusion_prime_register_stage_ramanujan_exact_cutoff
    (D : conclusion_prime_register_stage_ramanujan_layer_detection_data) (K : ℕ) :
    ((∀ D' : conclusion_prime_register_stage_ramanujan_layer_detection_data,
          D'.stagePrime = D.stagePrime →
          (∀ k : ℕ, 1 ≤ k → k ≤ K →
            conclusion_prime_register_stage_ramanujan_layer_detection_detected_indicator D' k =
              conclusion_prime_register_stage_ramanujan_layer_detection_detected_indicator D k) →
          D'.stageDepth = D.stageDepth) ↔
      D.stageDepth + 1 ≤ K) := by
  constructor
  · intro hunique
    by_contra hK
    have hKle : K ≤ D.stageDepth := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hK)
    let D' : conclusion_prime_register_stage_ramanujan_layer_detection_data :=
      { stagePrime := D.stagePrime
        stagePrime_gt_one := D.stagePrime_gt_one
        stageDepth := D.stageDepth + 1 }
    have hsame :
        ∀ k : ℕ, 1 ≤ k → k ≤ K →
          conclusion_prime_register_stage_ramanujan_layer_detection_detected_indicator D' k =
            conclusion_prime_register_stage_ramanujan_layer_detection_detected_indicator D k := by
      intro k _ hkK
      have hkD : k ≤ D.stageDepth := le_trans hkK hKle
      unfold conclusion_prime_register_stage_ramanujan_layer_detection_detected_indicator
        smithPrefixDelta
      simp [D', hkD, le_trans hkD (Nat.le_succ D.stageDepth)]
    have hdepth := hunique D' rfl hsame
    simp [D'] at hdepth
  · intro hK D' _ hsame
    refine le_antisymm ?_ ?_
    · by_contra hnot
      have hlt : D.stageDepth < D'.stageDepth := Nat.lt_of_not_ge hnot
      have hleD' : D.stageDepth + 1 ≤ D'.stageDepth := Nat.succ_le_iff.mpr hlt
      have hstep := hsame (D.stageDepth + 1) (by omega) hK
      unfold conclusion_prime_register_stage_ramanujan_layer_detection_detected_indicator
        smithPrefixDelta at hstep
      simp [hleD', Nat.not_succ_le_self D.stageDepth] at hstep
    · by_contra hnot
      have hlt : D'.stageDepth < D.stageDepth := Nat.lt_of_not_ge hnot
      have hleD : D'.stageDepth + 1 ≤ D.stageDepth := Nat.succ_le_iff.mpr hlt
      have hK' : D'.stageDepth + 1 ≤ K :=
        le_trans hleD (le_trans (Nat.le_succ D.stageDepth) hK)
      have hstep := hsame (D'.stageDepth + 1) (by omega) hK'
      unfold conclusion_prime_register_stage_ramanujan_layer_detection_detected_indicator
        smithPrefixDelta at hstep
      simp [hleD, Nat.not_succ_le_self D'.stageDepth] at hstep

end Omega.Conclusion
