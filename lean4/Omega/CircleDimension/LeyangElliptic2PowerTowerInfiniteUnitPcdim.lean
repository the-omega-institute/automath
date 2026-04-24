import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.CircleDimension.OddDivisibilityTowerHolographicSeparation

namespace Omega.CircleDimension

/-- Concrete denominator stages together with primitive-prime witnesses along the `2`-power tower. -/
structure LeyangElliptic2PowerTowerData where
  stageDenominators : ℕ → ℕ
  witnessPrime : ℕ → ℕ
  stagePos : ∀ k, 0 < stageDenominators k
  stageDivides : ∀ k, stageDenominators k ∣ stageDenominators (k + 1)
  witnessPrime_isPrime : ∀ k, Nat.Prime (witnessPrime k)
  witnessPrime_dvd_stage : ∀ k, witnessPrime k ∣ stageDenominators k
  witnessPrime_fresh : ∀ {j k}, j < k → ¬ witnessPrime k ∣ stageDenominators j

namespace LeyangElliptic2PowerTowerData

def strongDivisibility (D : LeyangElliptic2PowerTowerData) : Prop :=
  ∀ k, D.stageDenominators k ∣ D.stageDenominators (k + 1)

def exactOrderPrimeWitnesses (D : LeyangElliptic2PowerTowerData) : Prop :=
  ∀ k,
    Nat.Prime (D.witnessPrime k) ∧
      D.witnessPrime k ∣ D.stageDenominators k ∧
      ∀ j < k, ¬ D.witnessPrime k ∣ D.stageDenominators j

lemma stage_pos (D : LeyangElliptic2PowerTowerData) (k : ℕ) : 0 < D.stageDenominators k := by
  exact D.stagePos k

lemma stage_ne_zero (D : LeyangElliptic2PowerTowerData) (k : ℕ) : D.stageDenominators k ≠ 0 := by
  exact Nat.ne_of_gt (D.stage_pos k)

lemma stage_dvd_of_le (D : LeyangElliptic2PowerTowerData) {j k : ℕ} (h : j ≤ k) :
    D.stageDenominators j ∣ D.stageDenominators k := by
  induction h with
  | refl =>
      exact dvd_rfl
  | @step k h ih =>
      exact dvd_trans ih (D.stageDivides k)

lemma witnessPrime_dvd_stage_of_le (D : LeyangElliptic2PowerTowerData) {j k : ℕ} (h : j ≤ k) :
    D.witnessPrime j ∣ D.stageDenominators k := by
  exact dvd_trans (D.witnessPrime_dvd_stage j) (D.stage_dvd_of_le h)

lemma witnessPrime_injectiveOn_range (D : LeyangElliptic2PowerTowerData) (k : ℕ) :
    Set.InjOn D.witnessPrime {n | n < k + 1} := by
  intro a ha b hb hab
  rcases lt_trichotomy a b with hab_lt | rfl | hba_lt
  · exfalso
    exact D.witnessPrime_fresh hab_lt (by simpa [hab] using D.witnessPrime_dvd_stage a)
  · rfl
  · exfalso
    exact D.witnessPrime_fresh hba_lt (by simpa [hab] using D.witnessPrime_dvd_stage b)

def witnessSet (D : LeyangElliptic2PowerTowerData) (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).image D.witnessPrime

lemma witnessSet_subset_primeFactors (D : LeyangElliptic2PowerTowerData) (k : ℕ) :
    D.witnessSet k ⊆ (D.stageDenominators k).primeFactors := by
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨i, hi, rfl⟩
  have hi_le : i ≤ k := Nat.le_of_lt_succ (by simpa using hi)
  exact Nat.mem_primeFactors.mpr
    ⟨D.witnessPrime_isPrime i, D.witnessPrime_dvd_stage_of_le hi_le, D.stage_ne_zero k⟩

lemma witnessSet_card (D : LeyangElliptic2PowerTowerData) (k : ℕ) :
    (D.witnessSet k).card = k + 1 := by
  have hinj : Set.InjOn D.witnessPrime ((Finset.range (k + 1) : Finset ℕ) : Set ℕ) := by
    intro a ha b hb hab
    exact D.witnessPrime_injectiveOn_range k (by simpa using ha) (by simpa using hb) hab
  unfold witnessSet
  rw [Finset.card_image_of_injOn hinj]
  simp

lemma primeFactors_card_lower (D : LeyangElliptic2PowerTowerData) (k : ℕ) :
    k + 1 ≤ (D.stageDenominators k).primeFactors.card := by
  calc
    k + 1 = (D.witnessSet k).card := (D.witnessSet_card k).symm
    _ ≤ (D.stageDenominators k).primeFactors.card :=
      Finset.card_le_card (D.witnessSet_subset_primeFactors k)

end LeyangElliptic2PowerTowerData

open LeyangElliptic2PowerTowerData

/-- Paper label: `thm:cdim-leyang-elliptic-2power-tower-infinite-unit-pcdim`. -/
theorem paper_cdim_leyang_elliptic_2power_tower_infinite_unit_pcdim
    (D : LeyangElliptic2PowerTowerData) :
    D.strongDivisibility ∧ D.exactOrderPrimeWitnesses ∧
      pcdimInftyFromPrimeGrowth D.stageDenominators id = ⊤ := by
  refine ⟨D.stageDivides, ?_, ?_⟩
  · intro k
    exact ⟨D.witnessPrime_isPrime k, D.witnessPrime_dvd_stage k, fun j hj => D.witnessPrime_fresh hj⟩
  · have hunbounded : ∀ C, ∃ j, C < (D.stageDenominators j).primeFactors.card := by
      intro C
      refine ⟨C, ?_⟩
      have hlower := D.primeFactors_card_lower C
      simpa using lt_of_lt_of_le (Nat.lt_succ_self C) hlower
    simp [pcdimInftyFromPrimeGrowth, hunbounded]

end Omega.CircleDimension
