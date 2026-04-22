import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.KilloFoldBinEscortRenyiLogisticGeometry

namespace Omega.Folding

/-- The Bernoulli law on `{0,1}` extracted from the escort limit. -/
noncomputable def derivedBinfoldEscortBernoulliMass (q : ℝ) (b : Bool) : ℝ :=
  if b then killoEscortTheta q else 1 - killoEscortTheta q

/-- The natural parameter of the escort Bernoulli family. -/
noncomputable def derivedBinfoldEscortNaturalParameter (q : ℝ) : ℝ :=
  -((q + 1) * Real.log Real.goldenRatio)

/-- The log-partition function of the escort Bernoulli exponential family. -/
noncomputable def derivedBinfoldEscortLogPartition (q : ℝ) : ℝ :=
  Real.log (1 + Real.exp (derivedBinfoldEscortNaturalParameter q))

lemma killoEscortTheta_eq_exp_naturalParameter_over_partition (q : ℝ) :
    killoEscortTheta q =
      Real.exp (derivedBinfoldEscortNaturalParameter q) /
        (1 + Real.exp (derivedBinfoldEscortNaturalParameter q)) := by
  unfold killoEscortTheta derivedBinfoldEscortNaturalParameter
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero ((q + 1) * Real.log Real.goldenRatio)]
  ring

lemma one_sub_killoEscortTheta_eq_inverse_partition (q : ℝ) :
    1 - killoEscortTheta q =
      1 / (1 + Real.exp (derivedBinfoldEscortNaturalParameter q)) := by
  rw [killoEscortTheta_eq_exp_naturalParameter_over_partition]
  have hden : (1 + Real.exp (derivedBinfoldEscortNaturalParameter q) : ℝ) ≠ 0 := by
    positivity
  field_simp [hden]
  ring

/-- Paper-facing Bernoulli/exponential-family package for the escort limit law. -/
def DerivedBinfoldEscortFdivBernoulliExponentialFamilyStatement : Prop :=
  (∀ q : ℝ,
      derivedBinfoldEscortBernoulliMass q true = killoEscortTheta q ∧
        derivedBinfoldEscortBernoulliMass q false = 1 - killoEscortTheta q) ∧
    (∀ q : ℝ,
      killoEscortTheta q / (1 - killoEscortTheta q) =
        Real.exp (derivedBinfoldEscortNaturalParameter q)) ∧
    ∀ q : ℝ, ∀ b : Bool,
      derivedBinfoldEscortBernoulliMass q b =
        Real.exp
          ((if b then derivedBinfoldEscortNaturalParameter q else 0) -
            derivedBinfoldEscortLogPartition q)

/-- Paper label: `thm:derived-binfold-escort-fdiv-bernoulli-exponential-family`. The escort
temperature family is exactly the two-point Bernoulli law with parameter `killoEscortTheta`; its
odds ratio is `φ^{-(q+1)}`, and the same law has the standard one-parameter exponential-family
form on `{0,1}`. -/
theorem paper_derived_binfold_escort_fdiv_bernoulli_exponential_family :
    DerivedBinfoldEscortFdivBernoulliExponentialFamilyStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    simp [derivedBinfoldEscortBernoulliMass]
  · intro q
    calc
      killoEscortTheta q / (1 - killoEscortTheta q) =
          (Real.exp (derivedBinfoldEscortNaturalParameter q) /
              (1 + Real.exp (derivedBinfoldEscortNaturalParameter q))) /
            (1 / (1 + Real.exp (derivedBinfoldEscortNaturalParameter q))) := by
              nth_rewrite 1 [killoEscortTheta_eq_exp_naturalParameter_over_partition]
              rw [one_sub_killoEscortTheta_eq_inverse_partition]
      _ = Real.exp (derivedBinfoldEscortNaturalParameter q) := by
        have hden : (1 + Real.exp (derivedBinfoldEscortNaturalParameter q) : ℝ) ≠ 0 := by
          positivity
        field_simp [hden]
  · intro q b
    cases b with
    | false =>
        simp [derivedBinfoldEscortBernoulliMass]
        rw [one_sub_killoEscortTheta_eq_inverse_partition]
        have hpos : 0 < 1 + Real.exp (derivedBinfoldEscortNaturalParameter q) := by
          positivity
        unfold derivedBinfoldEscortLogPartition
        rw [Real.exp_neg, Real.exp_log hpos]
        simp [one_div]
    | true =>
        simp [derivedBinfoldEscortBernoulliMass]
        rw [killoEscortTheta_eq_exp_naturalParameter_over_partition]
        have hpos : 0 < 1 + Real.exp (derivedBinfoldEscortNaturalParameter q) := by
          positivity
        unfold derivedBinfoldEscortLogPartition
        rw [Real.exp_sub, Real.exp_log hpos]

end Omega.Folding
