import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.Conclusion.ZGDensityExactInhomogeneousMarkov
import Omega.Conclusion.ZGFinitePrimorialShadowCylinderRecovery

namespace Omega.DerivedConsequences

open Omega.Conclusion

/-- Concrete bounded-error packaging of the block-entropy asymptotic
`H_n = log p_n + log log p_n + O(1)`. -/
def derived_zg_finite_shadow_complete_but_zero_information_dimension_blockEntropyAsymptotic
    (primeScale blockEntropy : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    |blockEntropy n - (Real.log (primeScale n) + Real.log (Real.log (primeScale n)))| ≤ C

/-- The exact nonhomogeneous Markov package forwarded from the conclusion chapter. -/
def derived_zg_finite_shadow_complete_but_zero_information_dimension_markovPackage
    (w : ZGInhomogeneousMarkovWitness) : Prop :=
  (∀ n : ℕ,
    w.condProb n true = 0 ∧
      w.condProb n false =
        w.B (n + 1) / (w.p (n + 1) * w.A (n + 1) + w.B (n + 1))) ∧
    (∀ n : ℕ,
      w.B n / w.A n =
        w.p (n + 1) / (w.p (n + 1) + w.B (n + 1) / w.A (n + 1))) ∧
    (∀ n : ℕ,
      w.condProb n false =
        (w.B (n + 1) / w.A (n + 1)) /
          (w.p (n + 1) + w.B (n + 1) / w.A (n + 1)))

/-- Concrete obstruction to any stationary finite-order Markov description: along the all-zero
context, no positive transition value can stabilize forever. -/
def derived_zg_finite_shadow_complete_but_zero_information_dimension_nonstationaryMarkov
    (transition : ℕ → ℚ) : Prop :=
  ∀ c : ℚ, 0 < c → ∀ r : ℕ, ∃ n : ℕ, r ≤ n ∧ transition n ≠ c

private lemma derived_zg_finite_shadow_complete_but_zero_information_dimension_markovForward
    (w : ZGInhomogeneousMarkovWitness) :
    derived_zg_finite_shadow_complete_but_zero_information_dimension_markovPackage w :=
  paper_conclusion_zg_density_exact_inhomogeneous_markov w

private lemma derived_zg_finite_shadow_complete_but_zero_information_dimension_shadowForward :
    conclusion_zg_finite_primorial_shadow_cylinder_recovery_package :=
  paper_conclusion_zg_finite_primorial_shadow_cylinder_recovery

/-- Paper label: `thm:derived-zg-finite-shadow-complete-but-zero-information-dimension`. The
existing exact ZG Markov package and the finite primorial shadow recovery theorem combine with a
concrete entropy-growth witness, the zero information-dimension identity, and a concrete
nonstationary-Markov obstruction to give the stated derived consequence. -/
theorem paper_derived_zg_finite_shadow_complete_but_zero_information_dimension
    (w : ZGInhomogeneousMarkovWitness)
    (primeScale blockEntropy : ℕ → ℝ) (informationDimension : ℝ)
    (hEntropy :
      derived_zg_finite_shadow_complete_but_zero_information_dimension_blockEntropyAsymptotic
        primeScale blockEntropy)
    (hInfoDim : informationDimension = 0)
    (hNonstationary :
      derived_zg_finite_shadow_complete_but_zero_information_dimension_nonstationaryMarkov
        (fun n => w.condProb n false)) :
    derived_zg_finite_shadow_complete_but_zero_information_dimension_markovPackage w ∧
      conclusion_zg_finite_primorial_shadow_cylinder_recovery_package ∧
      derived_zg_finite_shadow_complete_but_zero_information_dimension_blockEntropyAsymptotic
        primeScale blockEntropy ∧
      informationDimension = 0 ∧
      derived_zg_finite_shadow_complete_but_zero_information_dimension_nonstationaryMarkov
        (fun n => w.condProb n false) := by
  exact ⟨derived_zg_finite_shadow_complete_but_zero_information_dimension_markovForward w,
    derived_zg_finite_shadow_complete_but_zero_information_dimension_shadowForward,
    hEntropy, hInfoDim, hNonstationary⟩

end Omega.DerivedConsequences
