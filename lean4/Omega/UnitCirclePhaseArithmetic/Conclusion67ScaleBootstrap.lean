import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.Conclusion66GramRamanujanDecomposition

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Concrete bootstrap datum for propagating a one-scale polynomial decay bound for the rational
Gram kernel along the regime `L = M²`. The package records positivity of the Fourier weights and a
covering estimate that transfers the seed decay to every larger scale. -/
structure Conclusion67ScaleBootstrapData where
  ψhat : ℤ → ℝ
  g : ℚ → ℂ
  opNorm : ℕ → ℝ
  seedScale : ℕ
  decayExponent : ℕ
  seedScale_ge_two : 2 ≤ seedScale
  psihat_nonneg : ∀ n : ℤ, 0 ≤ ψhat n
  bootstrapStep :
    ∀ ⦃M : ℕ⦄, seedScale ≤ M →
      opNorm M ≤ opNorm seedScale * (((seedScale : ℝ) / M) ^ decayExponent)
  seedDecay : opNorm seedScale ≤ 1 / (seedScale : ℝ) ^ decayExponent

namespace Conclusion67ScaleBootstrapData

/-- The scale-bootstrap package contains the denominator-layer Gram decomposition at the seed
scale, the positivity of the Fourier weights, and the propagated polynomial decay bound for every
larger scale in the regime `L = M²`. -/
def propagatesPolynomialDecay (D : Conclusion67ScaleBootstrapData) : Prop :=
  GramRamanujanDecompositionStatement D.seedScale (D.seedScale ^ 2) D.ψhat D.g ∧
    (∀ n : ℤ, 0 ≤ D.ψhat n) ∧
      ∀ M : ℕ, D.seedScale ≤ M → D.opNorm M ≤ 1 / (M : ℝ) ^ D.decayExponent

end Conclusion67ScaleBootstrapData

open Conclusion67ScaleBootstrapData

lemma seed_scale_decay_transfer {m M k : ℕ} (hm : m ≠ 0) (hM : M ≠ 0) :
    (1 / (m : ℝ) ^ k) * (((m : ℝ) / M) ^ k) = 1 / (M : ℝ) ^ k := by
  rw [div_pow]
  field_simp [pow_ne_zero k (show (m : ℝ) ≠ 0 by exact_mod_cast hm),
    pow_ne_zero k (show (M : ℝ) ≠ 0 by exact_mod_cast hM)]

/-- Paper label: `thm:conclusion67-scale-bootstrap`.
The one-scale decay certificate propagates from the seed scale to every larger denominator scale
once the Gram decomposition, positivity, and covering transfer are packaged together. -/
theorem paper_conclusion67_scale_bootstrap (D : Conclusion67ScaleBootstrapData) :
    D.propagatesPolynomialDecay := by
  refine ⟨paper_conclusion66_gram_ramanujan_decomposition D.seedScale (D.seedScale ^ 2) D.ψhat D.g,
    D.psihat_nonneg, ?_⟩
  intro M hM
  have hseed_ne : D.seedScale ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) D.seedScale_ge_two)
  have hM_ne : M ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (by decide : 0 < 2) D.seedScale_ge_two) hM)
  calc
    D.opNorm M ≤ D.opNorm D.seedScale * (((D.seedScale : ℝ) / M) ^ D.decayExponent) :=
      D.bootstrapStep hM
    _ ≤ (1 / (D.seedScale : ℝ) ^ D.decayExponent) *
          (((D.seedScale : ℝ) / M) ^ D.decayExponent) := by
      have hnonneg : 0 ≤ (((D.seedScale : ℝ) / M) ^ D.decayExponent) := by positivity
      exact mul_le_mul_of_nonneg_right D.seedDecay hnonneg
    _ = 1 / (M : ℝ) ^ D.decayExponent := seed_scale_decay_transfer hseed_ne hM_ne

end

end Omega.UnitCirclePhaseArithmetic
