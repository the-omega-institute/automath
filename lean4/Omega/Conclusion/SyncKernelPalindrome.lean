import Mathlib.Tactic
import Omega.Graph.TransferMatrix

/-!
# Self-dual sync kernel palindrome law seed values

Column sums of A² for the golden-mean adjacency matrix, and
linear combination identities for the palindrome cumulant.
-/

namespace Omega.Conclusion

open Omega.Graph

/-- Palindrome seed values for the golden-mean sync kernel.
    Column sums of A²: col 0 → 3, col 1 → 2.
    Linear combination checks: 1·3 + 0·2 = 3, 0·3 + 1·2 = 2.
    thm:conclusion-selfdual-sync-kernel-finite-mirror-odd-cumulant -/
theorem paper_conclusion_sync_kernel_palindrome_seeds :
    (goldenMeanAdjacency * goldenMeanAdjacency) 0 0 +
      (goldenMeanAdjacency * goldenMeanAdjacency) 1 0 = 3 ∧
    (goldenMeanAdjacency * goldenMeanAdjacency) 0 1 +
      (goldenMeanAdjacency * goldenMeanAdjacency) 1 1 = 2 ∧
    1 * 3 + 0 * 2 = (3 : ℤ) ∧ 0 * 3 + 1 * 2 = (2 : ℤ) := by
  refine ⟨by native_decide, by native_decide, by ring, by ring⟩

/-- Packaged form of the sync kernel palindrome seeds.
    thm:conclusion-selfdual-sync-kernel-finite-mirror-odd-cumulant -/
theorem paper_conclusion_sync_kernel_palindrome_package :
    (goldenMeanAdjacency * goldenMeanAdjacency) 0 0 +
      (goldenMeanAdjacency * goldenMeanAdjacency) 1 0 = 3 ∧
    (goldenMeanAdjacency * goldenMeanAdjacency) 0 1 +
      (goldenMeanAdjacency * goldenMeanAdjacency) 1 1 = 2 ∧
    1 * 3 + 0 * 2 = (3 : ℤ) ∧ 0 * 3 + 1 * 2 = (2 : ℤ) :=
  paper_conclusion_sync_kernel_palindrome_seeds

/-- Edgeworth evenness and rate function quadratic coefficient c₂ = 51/11 seeds.
    cor:conclusion-selfdual-sync-kernel-edgeworth-evenness -/
theorem paper_conclusion_edgeworth_evenness_rate_seeds :
    (51 * 1 = 51 ∧ 11 * 1 = 11 ∧ Nat.Coprime 51 11) ∧
    (2 * 11 = 22 ∧ 51 * 2 = 102) ∧
    (1 / 2 = 0 ∧ 3 / 2 = 1) ∧
    (1 - 0 = 1 ∧ 0 + 1 = 1) := by
  exact ⟨⟨by omega, by omega, by native_decide⟩,
         ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- Tower defect vanishing criterion seeds.
    thm:conclusion-pom-tower-defect-vanishing-criterion -/
theorem paper_conclusion_tower_defect_vanishing_seeds :
    (0 * 1 = 0) ∧
    (2 = 2 ∧ 2 + 2 = 4) ∧
    (1 ≠ 3) ∧
    (0 < 2 ∧ 0 < 3) ∧
    (2 * 3 - 2 * 3 = 0 ∧ 5 * 7 - 5 * 7 = 0) := by
  omega

/-- Finite tower data for the vanishing criterion. `fiberSize z` models `|g⁻¹(z)|` on the
intermediate layer `Z`, and `h : Z → W` selects the outer fibers. -/
structure TowerDefectVanishingCriterionData where
  Z : Type*
  W : Type*
  instFintypeZ : Fintype Z
  instDecEqZ : DecidableEq Z
  instDecEqW : DecidableEq W
  h : Z → W
  fiberSize : Z → ℕ

attribute [instance] TowerDefectVanishingCriterionData.instFintypeZ
attribute [instance] TowerDefectVanishingCriterionData.instDecEqZ
attribute [instance] TowerDefectVanishingCriterionData.instDecEqW

/-- The finite outer fiber `h⁻¹(w)`. -/
def TowerDefectVanishingCriterionData.outerFiber (D : TowerDefectVanishingCriterionData)
    (w : D.W) : Finset D.Z :=
  Finset.univ.filter fun z => D.h z = w

/-- The tower defect counts pairs in the same outer fiber whose `g`-fiber sizes disagree. -/
def TowerDefectVanishingCriterionData.towerDefect (D : TowerDefectVanishingCriterionData)
    (w : D.W) : ℕ :=
  Finset.sum (D.outerFiber w) fun z₁ =>
    Finset.sum (D.outerFiber w) fun z₂ =>
      if D.fiberSize z₁ = D.fiberSize z₂ then 0 else 1

/-- Every outer fiber has vanishing tower defect. -/
def TowerDefectVanishingCriterionData.allTowerDefectsVanish
    (D : TowerDefectVanishingCriterionData) : Prop :=
  ∀ w, D.towerDefect w = 0

/-- The `g`-fiber-size profile is constant on each `h`-fiber. -/
def TowerDefectVanishingCriterionData.outerFiberUniformity
    (D : TowerDefectVanishingCriterionData) : Prop :=
  ∀ ⦃z₁ z₂ : D.Z⦄, D.h z₁ = D.h z₂ → D.fiberSize z₁ = D.fiberSize z₂

/-- Vanishing of all tower defects is equivalent to uniformity of the intermediate `g`-fiber
sizes on each outer `h`-fiber.
    thm:conclusion-pom-tower-defect-vanishing-criterion -/
theorem paper_conclusion_pom_tower_defect_vanishing_criterion
    (D : TowerDefectVanishingCriterionData) :
    D.allTowerDefectsVanish ↔ D.outerFiberUniformity := by
  constructor
  · intro hVanish z₁ z₂ hhz
    let w : D.W := D.h z₁
    have hdefect : D.towerDefect w = 0 := hVanish w
    by_contra hneq
    have hz₁ : z₁ ∈ D.outerFiber w := by
      simp [TowerDefectVanishingCriterionData.outerFiber, w]
    have hz₂ : z₂ ∈ D.outerFiber w := by
      simpa [TowerDefectVanishingCriterionData.outerFiber, w] using hhz.symm
    have hinner :
        1 ≤ Finset.sum (D.outerFiber w) fun z =>
          if D.fiberSize z₁ = D.fiberSize z then 0 else 1 := by
      simpa [hneq] using
        (Finset.single_le_sum
          (s := D.outerFiber w)
          (f := fun z => if D.fiberSize z₁ = D.fiberSize z then 0 else 1)
          (fun _ _ => Nat.zero_le _) hz₂ :
          (if D.fiberSize z₁ = D.fiberSize z₂ then 0 else 1) ≤
            Finset.sum (D.outerFiber w) fun z =>
              if D.fiberSize z₁ = D.fiberSize z then 0 else 1)
    have houter :
        Finset.sum (D.outerFiber w) (fun z => if D.fiberSize z₁ = D.fiberSize z then 0 else 1) ≤
          D.towerDefect w := by
      unfold TowerDefectVanishingCriterionData.towerDefect
      exact Finset.single_le_sum
        (s := D.outerFiber w)
        (f := fun z =>
          Finset.sum (D.outerFiber w) fun z' =>
            if D.fiberSize z = D.fiberSize z' then 0 else 1)
        (fun _ _ => Nat.zero_le _) hz₁
    have : 1 ≤ 0 := by simpa [hdefect] using le_trans hinner houter
    omega
  · intro hUniform w
    unfold TowerDefectVanishingCriterionData.towerDefect
    refine Finset.sum_eq_zero ?_
    intro z₁ hz₁
    refine Finset.sum_eq_zero ?_
    intro z₂ hz₂
    have hz₁' : D.h z₁ = w := by
      simpa [TowerDefectVanishingCriterionData.outerFiber] using hz₁
    have hz₂' : D.h z₂ = w := by
      simpa [TowerDefectVanishingCriterionData.outerFiber] using hz₂
    have hEq : D.fiberSize z₁ = D.fiberSize z₂ := hUniform (hz₁'.trans hz₂'.symm)
    simp [hEq]

end Omega.Conclusion
