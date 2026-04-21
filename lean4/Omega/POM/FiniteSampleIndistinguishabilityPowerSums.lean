import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Omega.POM.PartitionMobiusEventInversion

open scoped BigOperators

namespace Omega.POM

/-- The `n`-th power sum of a finite sample law. -/
def samplePowerSum {α : Type*} [Fintype α] (μ : α → ℚ) (n : ℕ) : ℚ :=
  ∑ a, μ a ^ n

/-- The partition law attached to a family of equality blocks is the product of the corresponding
power sums. -/
def blockFamilyMass {α : Type*} [Fintype α] {k : ℕ} (μ : α → ℚ)
    (σ : Finset (Finset (Fin k))) : ℚ :=
  ∏ B ∈ σ, samplePowerSum μ B.card

/-- All finite families of subsets of `Fin k`, viewed as equality-pattern data. -/
def blockFamilyUniverse (k : ℕ) : Finset (Finset (Finset (Fin k))) :=
  (Finset.univ.powerset).powerset

/-- Any statistic that factors through the partition law is represented by a weight on the finite
universe of block families. -/
def symmetricPartitionStatistic {α : Type*} [Fintype α] (k : ℕ) (μ : α → ℚ)
    (T : Finset (Finset (Fin k)) → ℚ) : ℚ :=
  Finset.sum (blockFamilyUniverse k) fun σ => T σ * blockFamilyMass μ σ

/-- Equality-pattern indistinguishability on all block families of length `k`. -/
def partitionPatternIndistinguishable {α : Type*} [Fintype α] (k : ℕ) (μ ν : α → ℚ) : Prop :=
  ∀ σ ∈ blockFamilyUniverse k, blockFamilyMass μ σ = blockFamilyMass ν σ

/-- Indistinguishability for all fully symmetric statistics factoring through the partition law. -/
def symmetricStatisticIndistinguishable {α : Type*} [Fintype α] (k : ℕ) (μ ν : α → ℚ) : Prop :=
  ∀ T : Finset (Finset (Fin k)) → ℚ,
    symmetricPartitionStatistic k μ T = symmetricPartitionStatistic k ν T

/-- Indistinguishability of all power sums up to degree `k`. -/
def powerSumIndistinguishable {α : Type*} [Fintype α] (k : ℕ) (μ ν : α → ℚ) : Prop :=
  ∀ n ≤ k, samplePowerSum μ n = samplePowerSum ν n

/-- The initial block with cardinality `n`, embedded into `Fin k`. -/
def initialBlock (k n : ℕ) (hn : n ≤ k) : Finset (Fin k) :=
  Finset.univ.image fun i : Fin n => i.castLE hn

lemma initialBlock_card (k n : ℕ) (hn : n ≤ k) :
    (initialBlock k n hn).card = n := by
  classical
  unfold initialBlock
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b hab
    simpa using hab

lemma blockFamilyMass_singleton_initialBlock {α : Type*} [DecidableEq α] [Fintype α]
    (μ : α → ℚ) (k n : ℕ) (hn : n ≤ k) :
    blockFamilyMass μ ({initialBlock k n hn} : Finset (Finset (Fin k))) = samplePowerSum μ n := by
  unfold blockFamilyMass
  simp [initialBlock_card]

lemma partitionPatternIndistinguishable_imp_symmetricStatisticIndistinguishable
    {α : Type*} [Fintype α] {k : ℕ} {μ ν : α → ℚ}
    (h : partitionPatternIndistinguishable k μ ν) :
    symmetricStatisticIndistinguishable k μ ν := by
  intro T
  unfold symmetricPartitionStatistic
  refine Finset.sum_congr rfl ?_
  intro σ hσ
  rw [h σ hσ]

lemma symmetricStatistic_indicator_singleton {α : Type*} [Fintype α] (k : ℕ) (μ : α → ℚ)
    (B : Finset (Fin k)) :
    symmetricPartitionStatistic k μ
        (fun σ => if σ = ({B} : Finset (Finset (Fin k))) then 1 else 0) =
      blockFamilyMass μ ({B} : Finset (Finset (Fin k))) := by
  classical
  have hmem : ({B} : Finset (Finset (Fin k))) ∈ blockFamilyUniverse k := by
    simp [blockFamilyUniverse]
  simp [symmetricPartitionStatistic, hmem]

lemma symmetricStatisticIndistinguishable_imp_powerSumIndistinguishable
    {α : Type*} [DecidableEq α] [Fintype α] {k : ℕ} {μ ν : α → ℚ}
    (h : symmetricStatisticIndistinguishable k μ ν) :
    powerSumIndistinguishable k μ ν := by
  intro n hn
  let T : Finset (Finset (Fin k)) → ℚ :=
    fun σ => if σ = ({initialBlock k n hn} : Finset (Finset (Fin k))) then 1 else 0
  have hT := h T
  rw [symmetricStatistic_indicator_singleton k μ (initialBlock k n hn),
    symmetricStatistic_indicator_singleton k ν (initialBlock k n hn)] at hT
  simpa [blockFamilyMass_singleton_initialBlock, hn] using hT

lemma powerSumIndistinguishable_imp_partitionPatternIndistinguishable
    {α : Type*} [Fintype α] {k : ℕ} {μ ν : α → ℚ}
    (h : powerSumIndistinguishable k μ ν) :
    partitionPatternIndistinguishable k μ ν := by
  intro σ hσ
  unfold blockFamilyMass
  refine Finset.prod_congr rfl ?_
  intro B hB
  simpa using h B.card (by simpa using (Finset.card_le_univ B))

/-- Paper-facing finite-sample indistinguishability package: equality-pattern partition laws imply
equality of every fully symmetric statistic, those statistics recover the test masses of singleton
blocks, and those singleton block masses are exactly the power sums. Equivalently, the partition
law and the finite family of power sums determine each other.
    thm:pom-finite-sample-indistinguishability-power-sums -/
theorem paper_pom_finite_sample_indistinguishability_power_sums {α : Type*}
    [DecidableEq α] [Fintype α] (k : ℕ) (μ ν : α → ℚ) :
    (partitionPatternIndistinguishable k μ ν →
      symmetricStatisticIndistinguishable k μ ν) ∧
    (symmetricStatisticIndistinguishable k μ ν →
      powerSumIndistinguishable k μ ν) ∧
    (powerSumIndistinguishable k μ ν →
      partitionPatternIndistinguishable k μ ν) := by
  refine ⟨?_, ?_, ?_⟩
  · exact partitionPatternIndistinguishable_imp_symmetricStatisticIndistinguishable
  · exact symmetricStatisticIndistinguishable_imp_powerSumIndistinguishable
  · exact powerSumIndistinguishable_imp_partitionPatternIndistinguishable

end Omega.POM
