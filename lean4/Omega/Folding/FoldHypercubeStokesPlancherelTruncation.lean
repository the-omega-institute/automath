import Mathlib.Tactic
import Omega.Folding.HypercubeStokesPlancherelBoundaryEnergy
import Omega.Zeta.WalshParseval

namespace Omega.Folding

open Omega.Core
open Omega.Zeta.WalshParseval
open scoped BigOperators

noncomputable section

/-- Concrete hypercube data for the Stokes-Plancherel truncation package. The finite set `S`
determines the indicator observable on the `n`-cube, while `k` is the low-mode cutoff. -/
structure FoldHypercubeStokesPlancherelData where
  n : ℕ
  S : Finset (Word n)
  k : ℕ

namespace FoldHypercubeStokesPlancherelData

/-- The Fourier-Walsh coefficient of the indicator of `S`. -/
def coeff (D : FoldHypercubeStokesPlancherelData) (I : Finset (Fin D.n)) : ℤ :=
  walshBias (indicatorInt D.S) I

/-- The weighted Plancherel contribution of the mode `I`. -/
def boundaryModeEnergy (D : FoldHypercubeStokesPlancherelData) (I : Finset (Fin D.n)) : ℤ :=
  I.card * D.coeff I ^ 2

/-- All nonzero Fourier-Walsh modes. -/
def nonemptyModes (D : FoldHypercubeStokesPlancherelData) : Finset (Finset (Fin D.n)) :=
  (Finset.univ : Finset (Finset (Fin D.n))).erase ∅

/-- The singleton Fourier modes corresponding to the coordinate bit biases. -/
def singletonModes (D : FoldHypercubeStokesPlancherelData) : Finset (Finset (Fin D.n)) :=
  (Finset.univ : Finset (Fin D.n)).image fun i => ({i} : Finset (Fin D.n))

/-- The modes of size at most the truncation threshold `k`. -/
def lowModes (D : FoldHypercubeStokesPlancherelData) : Finset (Finset (Fin D.n)) :=
  D.nonemptyModes.filter fun I => I.card ≤ D.k

/-- The modes of size strictly larger than the truncation threshold `k`. -/
def highModes (D : FoldHypercubeStokesPlancherelData) : Finset (Finset (Fin D.n)) :=
  D.nonemptyModes.filter fun I => D.k < I.card

/-- The full nonzero weighted Walsh energy. -/
def totalBoundaryEnergy (D : FoldHypercubeStokesPlancherelData) : ℤ :=
  D.nonemptyModes.sum fun I => D.boundaryModeEnergy I

/-- The truncated low-mode contribution. -/
def lowModeEnergy (D : FoldHypercubeStokesPlancherelData) : ℤ :=
  D.lowModes.sum fun I => D.boundaryModeEnergy I

/-- The complementary high-mode contribution. -/
def highModeEnergy (D : FoldHypercubeStokesPlancherelData) : ℤ :=
  D.highModes.sum fun I => D.boundaryModeEnergy I

/-- Keeping only the singleton modes gives the coordinate-bias lower bound. -/
def squareDeviationLowerBound (D : FoldHypercubeStokesPlancherelData) : Prop :=
  (∑ i : Fin D.n, D.coeff ({i} : Finset (Fin D.n)) ^ 2) ≤ D.totalBoundaryEnergy

/-- Splitting the weighted Walsh energy into low and high modes leaves an exact nonnegative
residual identity. -/
def lowModeTruncationResidual (D : FoldHypercubeStokesPlancherelData) : Prop :=
  D.totalBoundaryEnergy = D.lowModeEnergy + D.highModeEnergy

lemma singleton_flux_readout (D : FoldHypercubeStokesPlancherelData) (i : Fin D.n) :
    ∑ w : Word D.n, (if w i = false then 1 else -1) * indicatorInt D.S w =
      D.coeff ({i} : Finset (Fin D.n)) := by
  simpa [coeff] using
    (paper_fold_hypercube_stokes_plancherel_boundary_energy D.n (indicatorInt D.S)).2.1 i

lemma boundaryModeEnergy_nonneg (D : FoldHypercubeStokesPlancherelData) (I : Finset (Fin D.n)) :
    0 ≤ D.boundaryModeEnergy I := by
  unfold boundaryModeEnergy
  exact mul_nonneg (by exact_mod_cast Nat.zero_le I.card) (sq_nonneg _)

lemma singletonModes_subset_nonemptyModes (D : FoldHypercubeStokesPlancherelData) :
    D.singletonModes ⊆ D.nonemptyModes := by
  intro I hI
  rcases Finset.mem_image.mp hI with ⟨i, _, rfl⟩
  simp [nonemptyModes]

lemma sum_singletonModes (D : FoldHypercubeStokesPlancherelData) :
    D.singletonModes.sum (fun I => D.boundaryModeEnergy I) =
      ∑ i : Fin D.n, D.coeff ({i} : Finset (Fin D.n)) ^ 2 := by
  unfold singletonModes
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro i _
    simp [boundaryModeEnergy, coeff]
  · intro i _ j _ hij
    have hi : i ∈ ({i} : Finset (Fin D.n)) := by simp
    have hj : i ∈ ({j} : Finset (Fin D.n)) := by simpa [hij] using hi
    simpa using hj

lemma totalBoundaryEnergy_split (D : FoldHypercubeStokesPlancherelData) :
    D.totalBoundaryEnergy = D.lowModeEnergy + D.highModeEnergy := by
  have hHigh :
      D.highModes = D.nonemptyModes.filter fun I => ¬ I.card ≤ D.k := by
    ext I
    simp [highModes, not_le]
  have hSplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := D.nonemptyModes)
      (f := fun I : Finset (Fin D.n) => D.boundaryModeEnergy I)
      (p := fun I : Finset (Fin D.n) => I.card ≤ D.k)
  simpa [totalBoundaryEnergy, lowModeEnergy, lowModes, highModeEnergy, hHigh] using hSplit.symm

/-- Paper-facing truncation package for the hypercube Stokes-Plancherel identity. The verified
singleton Stokes readout identifies the `|a| = 1` coordinate biases, and the full weighted
Walsh energy splits exactly into `|a| ≤ k` and `|a| > k` pieces.
    cor:fold-hypercube-stokes-plancherel-truncation -/
theorem paper_fold_hypercube_stokes_plancherel_truncation
    (D : FoldHypercubeStokesPlancherelData) :
    D.squareDeviationLowerBound ∧ D.lowModeTruncationResidual := by
  refine ⟨?_, totalBoundaryEnergy_split D⟩
  rw [squareDeviationLowerBound, ← sum_singletonModes D]
  exact Finset.sum_le_sum_of_subset_of_nonneg (singletonModes_subset_nonemptyModes D)
    (fun I _ _ => boundaryModeEnergy_nonneg D I)

end FoldHypercubeStokesPlancherelData

end

end Omega.Folding
