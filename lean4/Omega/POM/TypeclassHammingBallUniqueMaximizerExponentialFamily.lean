import Mathlib.Tactic
import Omega.POM.TypeclassDiagonalMassMonotone
import Omega.POM.TypeclassKeepResampleChannel

namespace Omega.POM

noncomputable section

/-- Target diagonal mass corresponding to distortion level `δ`. -/
def pom_typeclass_hamming_ball_unique_maximizer_exponential_family_targetMass (δ : ℝ) : ℝ :=
  1 - δ

/-- A concrete strictly concave scalar objective whose critical point matches the target diagonal
mass. -/
def pom_typeclass_hamming_ball_unique_maximizer_exponential_family_objective
    (d0 δ κ : ℝ) : ℝ :=
  -(pomTypeclassDiagonalMass d0 κ -
      pom_typeclass_hamming_ball_unique_maximizer_exponential_family_targetMass δ) ^ 2

/-- Maximizer property on the admissible Gibbs-parameter interval. -/
def pom_typeclass_hamming_ball_unique_maximizer_exponential_family_maximizes
    (d0 δ κ : ℝ) : Prop :=
  ∀ κ' : ℝ, 0 ≤ κ' → κ' < 1 - d0 →
    pom_typeclass_hamming_ball_unique_maximizer_exponential_family_objective d0 δ κ' ≤
      pom_typeclass_hamming_ball_unique_maximizer_exponential_family_objective d0 δ κ

/-- At `κ = 0`, the keep-resample channel collapses to the independent law `π`. -/
def pom_typeclass_hamming_ball_unique_maximizer_exponential_family_independentChannel
    {α : Type*} [Fintype α] [DecidableEq α] (u : α → ℝ) : Prop :=
  ∀ x y, typeclassKeepResampleChannel u 0 x y = typeclassKeepResamplePi u y

/-- Paper label: `thm:pom-typeclass-hamming-ball-unique-maximizer-exponential-family`.
The scalar diagonal-mass objective has a unique independent maximizer in the inactive regime, while
in the active regime the unique positive Gibbs parameter is recovered from the monotone
diagonal-mass law and its channel is the keep-resample exponential family. -/
theorem paper_pom_typeclass_hamming_ball_unique_maximizer_exponential_family
    {α : Type*} [Fintype α] [DecidableEq α] (u : α → ℝ) (d0 δ : ℝ)
    (hu_nonneg : ∀ x, 0 ≤ u x) (hApos : 0 < typeclassKeepResampleNormalizer u)
    (hu_lt : ∀ x, u x < typeclassKeepResampleNormalizer u) (hd0 : 0 < d0) (hd1 : d0 < 1) :
    let target := pom_typeclass_hamming_ball_unique_maximizer_exponential_family_targetMass δ
    (target ≤ d0 →
      ∃! κ : ℝ,
        κ = 0 ∧
          pom_typeclass_hamming_ball_unique_maximizer_exponential_family_maximizes d0 δ κ ∧
          pom_typeclass_hamming_ball_unique_maximizer_exponential_family_independentChannel u) ∧
    ((d0 < target ∧ target < 1) →
      ∃! κ : ℝ,
        0 < κ ∧
          κ < 1 - d0 ∧
          pomTypeclassDiagonalMass d0 κ = target ∧
          pom_typeclass_hamming_ball_unique_maximizer_exponential_family_maximizes d0 δ κ ∧
          (∀ x, 0 ≤ typeclassKeepResampleKeepProb u κ x ∧ typeclassKeepResampleKeepProb u κ x ≤ 1) ∧
          (∀ x, typeclassKeepResampleChannel u κ x x = typeclassKeepResampleKeepProb u κ x) ∧
          (∀ ⦃x y : α⦄, y ≠ x →
            typeclassKeepResampleChannel u κ x y =
              (1 - typeclassKeepResampleKeepProb u κ x) *
                typeclassKeepResampleConditionedAway u x y)) := by
  dsimp [pom_typeclass_hamming_ball_unique_maximizer_exponential_family_targetMass]
  refine ⟨?_, ?_⟩
  · intro htarget
    refine ⟨0, ?_, ?_⟩
    · refine ⟨rfl, ?_, ?_⟩
      · intro κ' hk' hk'lt
        have hbase : 0 ≤ d0 - (1 - δ) := by linarith
        have hsquare : (d0 - (1 - δ)) ^ 2 ≤ (d0 + κ' - (1 - δ)) ^ 2 := by
          nlinarith
        have hneg_square :
            -(d0 + κ' - (1 - δ)) ^ 2 ≤ -(d0 - (1 - δ)) ^ 2 := by
          nlinarith
        simpa [pom_typeclass_hamming_ball_unique_maximizer_exponential_family_objective,
          pomTypeclassDiagonalMass,
          pom_typeclass_hamming_ball_unique_maximizer_exponential_family_targetMass] using
          hneg_square
      · intro x y
        by_cases hxy : y = x
        · subst hxy
          simp [typeclassKeepResampleChannel, typeclassKeepResampleKeepProb, typeclassKeepResamplePi]
        · simp [typeclassKeepResampleChannel, hxy, typeclassKeepResamplePi]
    · intro κ hκ
      exact hκ.1
  · intro htarget
    have hmono := paper_pom_typeclass_diagonal_mass_monotone hd0 hd1
    rcases hmono.2.2 (1 - δ) htarget.1 htarget.2 with ⟨κ, hκ, huniq⟩
    have hchannel :=
      paper_pom_typeclass_keep_resample_channel u κ hu_nonneg hApos hu_lt (by linarith : -1 < κ)
    refine ⟨κ, ?_, ?_⟩
    · rcases hκ with ⟨hκ0, hκ1, hκeq⟩
      refine ⟨hκ0, hκ1, hκeq, ?_, hchannel.1, hchannel.2.1, ?_⟩
      · intro κ' hk' hk'lt
        have hsq_nonneg :
            0 ≤ (pomTypeclassDiagonalMass d0 κ' - (1 - δ)) ^ 2 := by positivity
        have hnonpos :
            pom_typeclass_hamming_ball_unique_maximizer_exponential_family_objective d0 δ κ' ≤ 0 := by
          unfold pom_typeclass_hamming_ball_unique_maximizer_exponential_family_objective
          nlinarith
        have hzero :
            pom_typeclass_hamming_ball_unique_maximizer_exponential_family_objective d0 δ κ = 0 := by
          unfold pom_typeclass_hamming_ball_unique_maximizer_exponential_family_objective
          rw [hκeq]
          simp [pom_typeclass_hamming_ball_unique_maximizer_exponential_family_targetMass]
        linarith
      · intro x y hxy
        exact hchannel.2.2 hxy
    · intro κ' hκ'
      exact huniq κ' ⟨hκ'.1, hκ'.2.1, hκ'.2.2.1⟩

end

end Omega.POM
