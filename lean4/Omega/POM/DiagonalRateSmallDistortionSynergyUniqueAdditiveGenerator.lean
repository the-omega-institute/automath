import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.RenyiHalfHellingerTensorAdditivity

namespace Omega.POM

/-- The tensor endpoint coefficient `C = A_{1/2}^2 - 1` used in the small-distortion package. -/
noncomputable def pom_small_distortion_synergy_unique_additive_generator_endpoint {α : Type*}
    [Fintype α] (w : α → ℝ) : ℝ :=
  pomHellingerHalfSum w ^ 2 - 1

/-- The additive generator obtained from the multiplicative endpoint law by `h(C) = log (1 + C)`.
-/
noncomputable def pom_small_distortion_synergy_unique_additive_generator_generator {α : Type*}
    [Fintype α] (w : α → ℝ) : ℝ :=
  Real.log (1 + pom_small_distortion_synergy_unique_additive_generator_endpoint w)

private theorem pom_small_distortion_synergy_unique_additive_generator_generator_eq_renyiHalf
    {α : Type*} [Fintype α] (w : α → ℝ) (hwpos : 0 < pomHellingerHalfSum w) :
    pom_small_distortion_synergy_unique_additive_generator_generator w = pomRenyiHalfEntropy w := by
  calc
    pom_small_distortion_synergy_unique_additive_generator_generator w =
        Real.log ((pomHellingerHalfSum w) ^ 2) := by
          simp [pom_small_distortion_synergy_unique_additive_generator_generator,
            pom_small_distortion_synergy_unique_additive_generator_endpoint]
    _ = Real.log (pomHellingerHalfSum w * pomHellingerHalfSum w) := by rw [pow_two]
    _ = Real.log (pomHellingerHalfSum w) + Real.log (pomHellingerHalfSum w) := by
          rw [Real.log_mul hwpos.ne' hwpos.ne']
    _ = pomRenyiHalfEntropy w := by
          simp [pomRenyiHalfEntropy, two_mul]

/-- Paper label: `thm:pom-small-distortion-synergy-unique-additive-generator`.

For the concrete Hellinger/Rényi-`1/2` endpoint, the multiplicative tensor law for
`1 + C = A_{1/2}^2` becomes additive after taking logs. The resulting additive generator is
exactly the Rényi-`1/2` entropy, so the tensor additivity law identifies the generator with the
Hellinger endpoint expression. -/
theorem paper_pom_small_distortion_synergy_unique_additive_generator {α β : Type*} [Fintype α]
    [Fintype β] (w : α → ℝ) (v : β → ℝ) (hw : ∀ a, 0 ≤ w a) (hv : ∀ b, 0 ≤ v b)
    (hwpos : 0 < pomHellingerHalfSum w) (hvpos : 0 < pomHellingerHalfSum v) :
    pom_small_distortion_synergy_unique_additive_generator_generator (pomTensorWeight w v) =
      pom_small_distortion_synergy_unique_additive_generator_generator w +
        pom_small_distortion_synergy_unique_additive_generator_generator v ∧
      pom_small_distortion_synergy_unique_additive_generator_generator w = pomRenyiHalfEntropy w ∧
      pom_small_distortion_synergy_unique_additive_generator_generator v = pomRenyiHalfEntropy v ∧
      pom_small_distortion_synergy_unique_additive_generator_generator (pomTensorWeight w v) =
        pomRenyiHalfEntropy (pomTensorWeight w v) := by
  have htensor_pos : 0 < pomHellingerHalfSum (pomTensorWeight w v) := by
    rw [pomHellingerHalfSum_tensor w v hw hv]
    exact mul_pos hwpos hvpos
  have hw_gen :
      pom_small_distortion_synergy_unique_additive_generator_generator w =
        pomRenyiHalfEntropy w :=
    pom_small_distortion_synergy_unique_additive_generator_generator_eq_renyiHalf w hwpos
  have hv_gen :
      pom_small_distortion_synergy_unique_additive_generator_generator v =
        pomRenyiHalfEntropy v :=
    pom_small_distortion_synergy_unique_additive_generator_generator_eq_renyiHalf v hvpos
  have htensor_gen :
      pom_small_distortion_synergy_unique_additive_generator_generator (pomTensorWeight w v) =
        pomRenyiHalfEntropy (pomTensorWeight w v) :=
    pom_small_distortion_synergy_unique_additive_generator_generator_eq_renyiHalf
      (pomTensorWeight w v) htensor_pos
  refine ⟨?_, hw_gen, hv_gen, htensor_gen⟩
  calc
    pom_small_distortion_synergy_unique_additive_generator_generator (pomTensorWeight w v) =
        pomRenyiHalfEntropy (pomTensorWeight w v) :=
      htensor_gen
    _ = pomRenyiHalfEntropy w + pomRenyiHalfEntropy v :=
      pomRenyiHalfEntropy_tensor_additivity w v hw hv hwpos hvpos
    _ = pom_small_distortion_synergy_unique_additive_generator_generator w +
          pom_small_distortion_synergy_unique_additive_generator_generator v := by
          rw [hw_gen, hv_gen]

end Omega.POM
