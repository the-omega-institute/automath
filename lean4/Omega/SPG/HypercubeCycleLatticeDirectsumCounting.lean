import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.SPG

noncomputable section

/-- Concrete data for the direct sum of `m` identical hypercube cycle lattices. The rank of each
summand is `rank`, the spanning-tree count is `treeCount`, and the counting radius is `radius`. -/
structure HypercubeCycleLatticeDirectsumData where
  m : ℕ
  rank : ℕ
  treeCount : ℕ
  radius : ℝ
  htree : 0 < treeCount

/-- One summand contributes covolume `√τ(G)`. -/
def componentCovolume (D : HypercubeCycleLatticeDirectsumData) : ℝ :=
  Real.sqrt D.treeCount

/-- Rank is additive under direct sum. -/
def directsumRank (D : HypercubeCycleLatticeDirectsumData) : ℕ :=
  ∑ _ : Fin D.m, D.rank

/-- Tree counts multiply across the `m` orthogonal summands. -/
def directsumTreeCount (D : HypercubeCycleLatticeDirectsumData) : ℕ :=
  ∏ _ : Fin D.m, D.treeCount

/-- Covolumes multiply across orthogonal direct sums. -/
def directsumCovolume (D : HypercubeCycleLatticeDirectsumData) : ℝ :=
  ∏ _ : Fin D.m, componentCovolume D

/-- The single-summand logarithmic counting law. -/
def componentCountingTerm (D : HypercubeCycleLatticeDirectsumData) : ℝ :=
  (D.rank : ℝ) * Real.log D.radius - Real.log (componentCovolume D)

/-- The direct-sum counting law inherits additively from the `m` orthogonal summands. -/
def directsumCountingTerm (D : HypercubeCycleLatticeDirectsumData) : ℝ :=
  ∑ _ : Fin D.m, componentCountingTerm D

/-- Concrete wrapper for the hypercube cycle-lattice direct-sum asymptotic package. -/
def HypercubeCycleLatticeDirectsumCountingLaw (D : HypercubeCycleLatticeDirectsumData) : Prop :=
  directsumRank D = D.m * D.rank ∧
    directsumTreeCount D = D.treeCount ^ D.m ∧
    Real.log (directsumCovolume D) = ((D.m : ℝ) / 2) * Real.log D.treeCount ∧
    directsumCountingTerm D =
      (directsumRank D : ℝ) * Real.log D.radius - Real.log (directsumCovolume D) ∧
    directsumCountingTerm D =
      (D.m * D.rank : ℝ) * Real.log D.radius - ((D.m : ℝ) / 2) * Real.log D.treeCount

/-- For an orthogonal direct sum of `m` copies of the same hypercube cycle lattice, ranks add,
tree counts and covolumes multiply, and the inherited counting asymptotic becomes
`m r log R - (m/2) log τ(G)`.
`cor:hypercube-cycle-lattice-directsum-counting` -/
theorem paper_hypercube_cycle_lattice_directsum_counting
    (D : HypercubeCycleLatticeDirectsumData) : HypercubeCycleLatticeDirectsumCountingLaw D := by
  have hRank : directsumRank D = D.m * D.rank := by
    simp [directsumRank]
  have hTree : directsumTreeCount D = D.treeCount ^ D.m := by
    simp [directsumTreeCount]
  have hCovPow : directsumCovolume D = (componentCovolume D) ^ D.m := by
    simp [directsumCovolume, componentCovolume]
  have hCompLog : Real.log (componentCovolume D) = (1 / 2 : ℝ) * Real.log D.treeCount := by
    unfold componentCovolume
    rw [Real.log_sqrt]
    · ring
    · positivity
  have hLogCovProd : Real.log (directsumCovolume D) = (D.m : ℝ) * Real.log (componentCovolume D) := by
    have hcomp_pos : 0 < componentCovolume D := by
      unfold componentCovolume
      exact Real.sqrt_pos.2 (by exact_mod_cast D.htree)
    rw [hCovPow]
    rw [show ((componentCovolume D) ^ D.m) = (componentCovolume D) ^ (D.m : ℝ) by
      rw [Real.rpow_natCast]]
    rw [Real.log_rpow hcomp_pos]
  have hLogCov : Real.log (directsumCovolume D) = ((D.m : ℝ) / 2) * Real.log D.treeCount := by
    rw [hLogCovProd, hCompLog]
    ring
  have hCounting :
      directsumCountingTerm D =
        (directsumRank D : ℝ) * Real.log D.radius - Real.log (directsumCovolume D) := by
    calc
      directsumCountingTerm D = (D.m : ℝ) * componentCountingTerm D := by
        simp [directsumCountingTerm]
      _ = (D.m : ℝ) * ((D.rank : ℝ) * Real.log D.radius) -
            (D.m : ℝ) * Real.log (componentCovolume D) := by
          simp [componentCountingTerm]
          ring
      _ = ((D.m : ℝ) * (D.rank : ℝ)) * Real.log D.radius - Real.log (directsumCovolume D) := by
          rw [hLogCovProd]
          ring
      _ = ((D.m * D.rank : ℕ) : ℝ) * Real.log D.radius - Real.log (directsumCovolume D) := by
          norm_num
      _ = (directsumRank D : ℝ) * Real.log D.radius - Real.log (directsumCovolume D) := by
          rw [hRank]
  have hExplicit :
      directsumCountingTerm D =
        (D.m * D.rank : ℝ) * Real.log D.radius - ((D.m : ℝ) / 2) * Real.log D.treeCount := by
    rw [hCounting, hRank, hLogCov]
    norm_num
  exact ⟨hRank, hTree, hLogCov, hCounting, hExplicit⟩

end

end Omega.SPG
