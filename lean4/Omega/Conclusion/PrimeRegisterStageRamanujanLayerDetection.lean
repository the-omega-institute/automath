import Mathlib.Tactic
import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Conclusion

open Omega.Zeta

/-- Concrete prime-register stage data: a distinguished prime and a single detected depth. -/
structure conclusion_prime_register_stage_ramanujan_layer_detection_data where
  stagePrime : ℕ
  stagePrime_gt_one : 1 < stagePrime
  stageDepth : ℕ

/-- The prime-power stage modulus `M = p^ℓ`. -/
def conclusion_prime_register_stage_ramanujan_layer_detection_stage_modulus
    (D : conclusion_prime_register_stage_ramanujan_layer_detection_data) : ℕ :=
  D.stagePrime ^ D.stageDepth

/-- The Ramanujan-layer detector specialized to the singleton stage profile `{ℓ}`. -/
def conclusion_prime_register_stage_ramanujan_layer_detection_detected_indicator
    (D : conclusion_prime_register_stage_ramanujan_layer_detection_data) (k : ℕ) : ℕ :=
  smithPrefixDelta (fun _ : Fin 1 => D.stageDepth) k

/-- The finite set of detected exponents up to the stage depth. -/
def conclusion_prime_register_stage_ramanujan_layer_detection_detected_layers
    (D : conclusion_prime_register_stage_ramanujan_layer_detection_data) : Finset ℕ :=
  (Finset.range (D.stageDepth + 1)).filter fun k =>
    conclusion_prime_register_stage_ramanujan_layer_detection_detected_indicator D k = 1

/-- The maximal exponent detected by the stage audit. -/
def conclusion_prime_register_stage_ramanujan_layer_detection_detected_depth
    (D : conclusion_prime_register_stage_ramanujan_layer_detection_data) : ℕ :=
  (conclusion_prime_register_stage_ramanujan_layer_detection_detected_layers D).sup id

/-- Paper-facing stage-detection package: the singleton prime-power Ramanujan detector is exactly
the indicator of `k ≤ ℓ`, and the largest detected exponent is the stage depth itself. -/
def conclusion_prime_register_stage_ramanujan_layer_detection_statement
    (D : conclusion_prime_register_stage_ramanujan_layer_detection_data) : Prop :=
  (∀ k : ℕ,
    conclusion_prime_register_stage_ramanujan_layer_detection_detected_indicator D k =
      if k ≤ D.stageDepth then 1 else 0) ∧
    conclusion_prime_register_stage_ramanujan_layer_detection_detected_depth D = D.stageDepth ∧
    conclusion_prime_register_stage_ramanujan_layer_detection_stage_modulus D =
      D.stagePrime ^ D.stageDepth

private lemma conclusion_prime_register_stage_ramanujan_layer_detection_indicator_eq
    (D : conclusion_prime_register_stage_ramanujan_layer_detection_data) (k : ℕ) :
    conclusion_prime_register_stage_ramanujan_layer_detection_detected_indicator D k =
      if k ≤ D.stageDepth then 1 else 0 := by
  unfold conclusion_prime_register_stage_ramanujan_layer_detection_detected_indicator
    smithPrefixDelta
  by_cases hk : k ≤ D.stageDepth
  · simp [hk]
  · simp [hk]

private lemma conclusion_prime_register_stage_ramanujan_layer_detection_detected_layers_top_mem
    (D : conclusion_prime_register_stage_ramanujan_layer_detection_data) :
    D.stageDepth ∈ conclusion_prime_register_stage_ramanujan_layer_detection_detected_layers D := by
  simp [conclusion_prime_register_stage_ramanujan_layer_detection_detected_layers,
    conclusion_prime_register_stage_ramanujan_layer_detection_indicator_eq]

private lemma conclusion_prime_register_stage_ramanujan_layer_detection_detected_depth_eq
    (D : conclusion_prime_register_stage_ramanujan_layer_detection_data) :
    conclusion_prime_register_stage_ramanujan_layer_detection_detected_depth D = D.stageDepth := by
  refine le_antisymm ?_ ?_
  · unfold conclusion_prime_register_stage_ramanujan_layer_detection_detected_depth
    refine Finset.sup_le ?_
    intro k hk
    have hkle : k ≤ D.stageDepth := by
      simp [conclusion_prime_register_stage_ramanujan_layer_detection_detected_layers] at hk
      exact hk.1
    exact hkle
  · unfold conclusion_prime_register_stage_ramanujan_layer_detection_detected_depth
    simpa using
      (Finset.le_sup
        (s := conclusion_prime_register_stage_ramanujan_layer_detection_detected_layers D)
        (f := id)
        (conclusion_prime_register_stage_ramanujan_layer_detection_detected_layers_top_mem D))

/-- Paper label: `thm:conclusion-prime-register-stage-ramanujan-layer-detection`. The singleton
prime-power stage profile has detector `1_{k ≤ ℓ}` and therefore the maximal detected depth is
exactly the stage exponent `ℓ`; the stage modulus is the concrete prime power `p^ℓ`. -/
theorem paper_conclusion_prime_register_stage_ramanujan_layer_detection
    (D : conclusion_prime_register_stage_ramanujan_layer_detection_data) :
    conclusion_prime_register_stage_ramanujan_layer_detection_statement D := by
  refine ⟨conclusion_prime_register_stage_ramanujan_layer_detection_indicator_eq D,
    conclusion_prime_register_stage_ramanujan_layer_detection_detected_depth_eq D, rfl⟩

end Omega.Conclusion
