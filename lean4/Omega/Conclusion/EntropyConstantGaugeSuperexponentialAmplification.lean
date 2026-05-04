import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Data marker for the entropy constant gauge amplification identities. -/
abbrev conclusion_entropy_constant_gauge_superexponential_amplification_data := Unit

noncomputable def conclusion_entropy_constant_gauge_superexponential_amplification_logVolume
    (δ : ℕ → ℝ) (m : ℕ) : ℝ :=
  (2 : ℝ) ^ m * ((m : ℝ) * Real.log (2 / Real.goldenRatio) - δ m - 1)

namespace conclusion_entropy_constant_gauge_superexponential_amplification_data

def single_mechanism_asymptotic
    (_D : conclusion_entropy_constant_gauge_superexponential_amplification_data) : Prop :=
  ∀ (δ : ℕ → ℝ) (m : ℕ),
    conclusion_entropy_constant_gauge_superexponential_amplification_logVolume δ m =
      (2 : ℝ) ^ m * ((m : ℝ) * Real.log (2 / Real.goldenRatio) - δ m - 1)

def two_mechanism_ratio_asymptotic
    (_D : conclusion_entropy_constant_gauge_superexponential_amplification_data) : Prop :=
  ∀ (δ₁ δ₂ : ℕ → ℝ) (c : ℝ) (m : ℕ),
    δ₁ m - δ₂ m = c →
      conclusion_entropy_constant_gauge_superexponential_amplification_logVolume δ₁ m -
          conclusion_entropy_constant_gauge_superexponential_amplification_logVolume δ₂ m =
        -c * (2 : ℝ) ^ m

end conclusion_entropy_constant_gauge_superexponential_amplification_data

/-- Paper label: `cor:conclusion-entropy-constant-gauge-superexponential-amplification`. -/
theorem paper_conclusion_entropy_constant_gauge_superexponential_amplification
    (D : conclusion_entropy_constant_gauge_superexponential_amplification_data) :
    D.single_mechanism_asymptotic ∧ D.two_mechanism_ratio_asymptotic := by
  refine ⟨?_, ?_⟩
  · intro δ m
    rfl
  · intro δ₁ δ₂ c m hc
    unfold conclusion_entropy_constant_gauge_superexponential_amplification_logVolume
    rw [← hc]
    ring

end Omega.Conclusion
