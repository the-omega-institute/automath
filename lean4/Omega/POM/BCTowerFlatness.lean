import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete adjacent-fiber data for a Beck-Chevalley tower along one visible branch. The
`stageCard i` record the adjacent fiber cardinalities, while `pairCard i` records the two-step
composite fiber cardinality across the `i`-th adjacent pair. -/
structure BCTowerFlatnessData where
  depth : ℕ
  stageCard : Fin depth → ℕ
  stageCard_pos : ∀ i, 0 < stageCard i
  pairCard : Fin (depth - 1) → ℕ
  pairCard_pos : ∀ i, 0 < pairCard i

namespace BCTowerFlatnessData

/-- Left endpoint of an adjacent pair in the tower. -/
def leftIndex (D : BCTowerFlatnessData) (i : Fin (D.depth - 1)) : Fin D.depth :=
  ⟨i.1, by omega⟩

/-- Right endpoint of an adjacent pair in the tower. -/
def rightIndex (D : BCTowerFlatnessData) (i : Fin (D.depth - 1)) : Fin D.depth :=
  ⟨i.1 + 1, by omega⟩

/-- The multiplicative adjacent-fiber size predicted by flatness. -/
def adjacentProduct (D : BCTowerFlatnessData) (i : Fin (D.depth - 1)) : ℕ :=
  D.stageCard (D.leftIndex i) * D.stageCard (D.rightIndex i)

lemma adjacentProduct_pos (D : BCTowerFlatnessData) (i : Fin (D.depth - 1)) :
    0 < D.adjacentProduct i := by
  dsimp [adjacentProduct]
  exact Nat.mul_pos (D.stageCard_pos _) (D.stageCard_pos _)

/-- Pointwise sequential-vs-direct logarithmic ratio on one adjacent pair. -/
def adjacentLogRatio (D : BCTowerFlatnessData) (i : Fin (D.depth - 1)) : ℝ :=
  Real.log (D.pairCard i : ℝ) - Real.log (D.adjacentProduct i : ℝ)

/-- Squared curvature defect of one adjacent pair. -/
def adjacentCurvature (D : BCTowerFlatnessData) (i : Fin (D.depth - 1)) : ℝ :=
  (D.adjacentLogRatio i) ^ 2

/-- Total tower defect, obtained by summing the adjacent squared curvatures. -/
def totalDefect (D : BCTowerFlatnessData) : ℝ :=
  ∑ i, D.adjacentCurvature i

/-- The sequential lift agrees with the direct lift precisely when the total defect vanishes. -/
def sequentialLiftEqDirectLift (D : BCTowerFlatnessData) : Prop :=
  D.totalDefect = 0

/-- Flatness means that every adjacent composite fiber size is multiplicative. -/
def multiplicativeFiberProfile (D : BCTowerFlatnessData) : Prop :=
  ∀ i, D.pairCard i = D.adjacentProduct i

lemma adjacentCurvature_nonneg (D : BCTowerFlatnessData) (i : Fin (D.depth - 1)) :
    0 ≤ D.adjacentCurvature i := by
  dsimp [adjacentCurvature]
  positivity

lemma adjacentCurvature_eq_zero_of_multiplicative (D : BCTowerFlatnessData)
    (hmult : D.multiplicativeFiberProfile) (i : Fin (D.depth - 1)) :
    D.adjacentCurvature i = 0 := by
  have hprod_ne : (D.adjacentProduct i : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.adjacentProduct_pos i)
  have hlog : D.adjacentLogRatio i = 0 := by
    unfold adjacentLogRatio
    rw [hmult i]
    norm_num
  unfold adjacentCurvature
  rw [hlog]
  norm_num

lemma multiplicative_of_adjacentLogRatio_zero (D : BCTowerFlatnessData) (i : Fin (D.depth - 1))
    (hzero : D.adjacentLogRatio i = 0) :
    D.pairCard i = D.adjacentProduct i := by
  have hpair_pos : 0 < (D.pairCard i : ℝ) := by
    exact_mod_cast D.pairCard_pos i
  have hprod_pos : 0 < (D.adjacentProduct i : ℝ) := by
    exact_mod_cast D.adjacentProduct_pos i
  have hlog_eq : Real.log (D.pairCard i : ℝ) = Real.log (D.adjacentProduct i : ℝ) := by
    dsimp [adjacentLogRatio] at hzero
    linarith
  have hexp := congrArg Real.exp hlog_eq
  have hreal : (D.pairCard i : ℝ) = (D.adjacentProduct i : ℝ) := by
    simpa [Real.exp_log hpair_pos, Real.exp_log hprod_pos] using hexp
  exact_mod_cast hreal

end BCTowerFlatnessData

/-- Paper label: `thm:pom-bc-tower-flatness`.
Vanishing of the total adjacent curvature defect is equivalent to multiplicativity of every
adjacent composite fiber size. -/
theorem paper_pom_bc_tower_flatness (D : BCTowerFlatnessData) :
    D.sequentialLiftEqDirectLift ↔ D.multiplicativeFiberProfile := by
  constructor
  · intro hseq i
    have hle : D.adjacentCurvature i ≤ D.totalDefect := by
      unfold BCTowerFlatnessData.totalDefect
      exact Finset.single_le_sum
        (fun j _ => D.adjacentCurvature_nonneg j)
        (by simp)
    have hcurv_zero : D.adjacentCurvature i = 0 := by
      apply le_antisymm
      · rw [BCTowerFlatnessData.sequentialLiftEqDirectLift] at hseq
        simpa [hseq] using hle
      · exact D.adjacentCurvature_nonneg i
    have hratio_zero : D.adjacentLogRatio i = 0 := by
      have hsquare_zero : (D.adjacentLogRatio i) ^ 2 = 0 := by
        simpa [BCTowerFlatnessData.adjacentCurvature] using hcurv_zero
      exact sq_eq_zero_iff.mp hsquare_zero
    exact D.multiplicative_of_adjacentLogRatio_zero i hratio_zero
  · intro hmult
    rw [BCTowerFlatnessData.sequentialLiftEqDirectLift, BCTowerFlatnessData.totalDefect]
    refine Finset.sum_eq_zero ?_
    intro i hi
    exact D.adjacentCurvature_eq_zero_of_multiplicative hmult i

end

end Omega.POM
