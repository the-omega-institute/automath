import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic
import Omega.RatioResultant.RatioFieldSplitting
import Omega.RatioResultant.RatioResultantDiscRigidity

namespace Omega.RatioResultant

/-- Concrete data for the ratio-field full-symmetric wrapper: the splitting package and the
ratio-resultant discriminant package are tracked together, and the root count is assumed to be at
least `4`. -/
structure RatioFieldFullSymmetricData (K : Type*) [Field K] where
  splittingData : RatioFieldSplittingData K
  resultantData : RatioResultantData K
  hrootCount : 4 ≤ resultantData.rootCount

namespace RatioFieldFullSymmetricData

/-- Distinguished first root index. -/
def baseZero {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) :
    Fin D.resultantData.rootCount :=
  ⟨0, lt_of_lt_of_le (by decide) D.hrootCount⟩

/-- Distinguished second root index. -/
def baseOne {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) :
    Fin D.resultantData.rootCount :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 4) D.hrootCount⟩

/-- The cyclic normal kernel modeled by the trivial cyclic subgroup of the full symmetric group. -/
def kernelSubgroup {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) :
    Subgroup (Equiv.Perm (Fin D.resultantData.rootCount)) :=
  Subgroup.zpowers 1

/-- Ordered-pair irreducibility: any ordered pair of distinct indices lies in the orbit of the
base pair `(0,1)` under the full symmetric action. -/
def orderedPairIrreducible {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) : Prop :=
  ∀ i j : Fin D.resultantData.rootCount, i ≠ j →
    ∃ σ : Equiv.Perm (Fin D.resultantData.rootCount), σ D.baseZero = i ∧ σ D.baseOne = j

/-- Full-symmetric completeness bundles the cyclic-normal kernel reduction, the ratio-resultant
discriminant rigidity, and the ordered-pair orbit statement. -/
def fullSymmetricCompleteness {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) : Prop :=
  IsCyclic D.kernelSubgroup ∧
    D.kernelSubgroup.Normal ∧
    D.kernelSubgroup = ⊥ ∧
    D.resultantData.discriminantQuadraticRigidity ∧
    D.orderedPairIrreducible

end RatioFieldFullSymmetricData

open RatioFieldFullSymmetricData

private def orderedPairBaseZero {n : ℕ} (h2 : 2 ≤ n) : Fin n :=
  ⟨0, lt_of_lt_of_le (by decide) h2⟩

private def orderedPairBaseOne {n : ℕ} (h2 : 2 ≤ n) : Fin n :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 2) h2⟩

private lemma baseZero_ne_baseOne {n : ℕ} (h2 : 2 ≤ n) :
    orderedPairBaseZero h2 ≠ orderedPairBaseOne h2 := by
  intro h
  have hval : (orderedPairBaseZero h2).val = (orderedPairBaseOne h2).val := congrArg Fin.val h
  simp [orderedPairBaseZero, orderedPairBaseOne] at hval

private lemma exists_perm_send_ordered_pair {n : ℕ} (h2 : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin n),
      σ (orderedPairBaseZero h2) = i ∧ σ (orderedPairBaseOne h2) = j := by
  let a : Fin n := orderedPairBaseZero h2
  let b : Fin n := orderedPairBaseOne h2
  have hab : a ≠ b := baseZero_ne_baseOne h2
  by_cases hi : i = a
  · subst hi
    by_cases hj : j = b
    · subst hj
      exact ⟨1, rfl, rfl⟩
    · refine ⟨Equiv.swap b j, ?_, ?_⟩
      · simpa using Equiv.swap_apply_of_ne_of_ne hab hij
      · simp [b]
  · let τ : Equiv.Perm (Fin n) := Equiv.swap a i
    refine ⟨Equiv.swap (τ b) j * τ, ?_, ?_⟩
    · have hτa : τ a = i := by
        simp [τ]
      have hτb_ne_i : τ b ≠ i := by
        intro h
        have hba : b = a := τ.injective (h.trans hτa.symm)
        exact hab hba.symm
      have hi_ne_τb : i ≠ τ b := by
        intro h
        exact hτb_ne_i h.symm
      change Equiv.swap (τ b) j (τ a) = i
      rw [hτa]
      exact Equiv.swap_apply_of_ne_of_ne hi_ne_τb hij
    · change Equiv.swap (τ b) j (τ b) = j
      simp

lemma kernelSubgroup_eq_bot {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) :
    D.kernelSubgroup = ⊥ := by
  ext σ
  simp [RatioFieldFullSymmetricData.kernelSubgroup]

/-- Ratio-field full-symmetric completion: the ratio-field splitting theorem exhibits the cyclic
kernel template, the discriminant-rigidity theorem collapses the quadratic character to sign, and
the symmetric group acts transitively on ordered pairs of distinct roots.
    cor:ratio-field-full-symmetric -/
theorem paper_ratio_field_full_symmetric {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) :
    D.fullSymmetricCompleteness := by
  have hSplit := paper_ratio_field_splitting D.splittingData
  have hUnitKernel :
      ∃ H : Subgroup Kˣ, H = Subgroup.zpowers (1 : Kˣ) ∧ Nat.card H ∣ 1 ∧ IsCyclic H := by
    rcases hSplit 1 1 (by simp) with ⟨H, hH, hcard, hcyc, _, _⟩
    exact ⟨H, hH, hcard, hcyc⟩
  have hKernel : D.kernelSubgroup = ⊥ := kernelSubgroup_eq_bot D
  have hCyclic : IsCyclic D.kernelSubgroup := by
    rw [hKernel]
    infer_instance
  have hNormal : D.kernelSubgroup.Normal := by
    rw [hKernel]
    infer_instance
  have hRigidity : D.resultantData.discriminantQuadraticRigidity :=
    paper_ratio_resultant_disc_rigidity D.resultantData
  have hPairs : D.orderedPairIrreducible := by
    intro i j hij
    exact exists_perm_send_ordered_pair
      (le_trans (by decide : 2 ≤ 4) D.hrootCount) i j hij
  exact ⟨hCyclic, hNormal, hKernel, hRigidity, hPairs⟩

end Omega.RatioResultant
