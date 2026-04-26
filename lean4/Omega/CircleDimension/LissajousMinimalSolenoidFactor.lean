import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.CircleDimension.ArithmeticSingularRingOneParameterSubgroups
import Omega.CircleDimension.LissajousPhaseCirclePrimeLedgerKernel
import Omega.CircleDimension.LocalizedGsDualCompleteClassification
import Omega.CircleDimension.SolenoidKernelProductZp

namespace Omega.CircleDimension

open LocalizedGsEmbeddingOrderData

/-- The finite prime set extracted from the common Lissajous frequency ledger. -/
def lissajousMinimalPrimeSet (a b : ℕ) : Finset ℕ :=
  (lissajousPrimeLedgerKernel a b).primeFactors

/-- The one-parameter subgroup coming from the constant inclusion `G_S ↪ ℝ`. -/
def lissajousMinimalOneParameterSubgroup (a b : ℕ) :
    arithmeticSingularRingOneParameterSubgroups (lissajousMinimalPrimeSet a b) :=
  subgroupOfTorusFrequencyVector (fun _ => 1)

private lemma lissajousMinimalPrimeSet_primes (a b : ℕ) (ha : 0 < a) :
    ∀ p ∈ lissajousMinimalPrimeSet a b, Nat.Prime p := by
  intro p hp
  unfold lissajousMinimalPrimeSet at hp
  have hgcd_ne_zero : Nat.gcd a b ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left b ha)
  exact Nat.prime_of_mem_primeFactors hp

private def lissajousMinimalEmbeddingData (a b : ℕ) (ha : 0 < a)
    (T : Finset ℕ) (hT : ∀ p ∈ T, Nat.Prime p) : LocalizedGsEmbeddingOrderData where
  S := lissajousMinimalPrimeSet a b
  T := T
  S_primes := lissajousMinimalPrimeSet_primes a b ha
  T_primes := hT

/-- Paper-facing package for the minimal solenoid factor of the `(a,b)`-Lissajous flow. The prime
support is the common prime ledger of the two frequencies, the Pontryagin dual kernel is the
product of the corresponding `p`-adic coordinates, the additive inclusion into `ℝ` gives the
constant one-parameter subgroup, and quotient maps to other finite-prime solenoids are exactly
the dualized subgroup inclusions. -/
def LissajousMinimalSolenoidFactorStatement (a b : ℕ) : Prop :=
  let S := lissajousMinimalPrimeSet a b
  S = (lissajousPrimeLedgerKernel a b).primeFactors ∧
    (∀ p ∈ S, Nat.Prime p) ∧
    Nonempty (SolenoidProjectionKernel S ≃ SolenoidKernelProductZpModel S) ∧
    (∃ G : arithmeticSingularRingOneParameterSubgroups S, ∀ p : S, G.torusFrequency p = 1) ∧
    (∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) →
      (compatibleDualSurjection S T ↔ S ⊆ T)) ∧
    (∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) →
      ((compatibleDualSurjection S T ∧ compatibleDualSurjection T S) ↔ S = T))

/-- Paper label: `thm:cdim-lissajous-minimal-solenoid-factor`. -/
theorem paper_cdim_lissajous_minimal_solenoid_factor (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    LissajousMinimalSolenoidFactorStatement a b := by
  have _ := hb
  dsimp [LissajousMinimalSolenoidFactorStatement]
  refine ⟨rfl, lissajousMinimalPrimeSet_primes a b ha,
    (paper_cdim_solenoid_kernel_product_zp (lissajousMinimalPrimeSet a b)).2, ?_, ?_, ?_⟩
  · refine ⟨lissajousMinimalOneParameterSubgroup a b, ?_⟩
    intro p
    rfl
  · intro T hT
    exact
      (paper_cdim_localized_gs_embedding_order (lissajousMinimalEmbeddingData a b ha T hT)).2
  · intro T hT
    simpa [compatibleDualSurjection] using
      (paper_cdim_localized_gs_dual_complete_classification
        (lissajousMinimalEmbeddingData a b ha T hT))

end Omega.CircleDimension
