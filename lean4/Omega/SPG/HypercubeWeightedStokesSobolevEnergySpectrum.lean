import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
import Omega.SPG.HypercubeWeightedWalshStokes

namespace Omega.SPG

open scoped BigOperators

noncomputable section

/-- The complex Walsh coefficient of `f` at the frequency set `I`, using the weighted Stokes
normalization from the hypercube face package. -/
def weightedWalshFourierCoeff {n : Nat} (f : Omega.Word n -> Complex) (I : Finset (Fin n)) :
    Complex :=
  ∑ ω : Omega.Word n, ((weightedWalshCharacter I ω : ℝ) : Complex) * f ω

/-- The weighted spectral contribution of the Walsh mode `I`. -/
def weightedWalshSpectralDensity {n : Nat} (f : Omega.Word n -> Complex) (w : Fin n -> Real)
    (I : Finset (Fin n)) : Real :=
  |weightedWalshEigenvalue I w| * Complex.normSq (weightedWalshFourierCoeff f I)

/-- Total weighted spectral energy over all Walsh modes on the `n`-cube. -/
def hypercubeWeightedStokesDirichletEnergy {n : Nat} (f : Omega.Word n -> Complex)
    (w : Fin n -> Real) : Real :=
  Finset.sum ((Finset.univ : Finset (Fin n)).powerset) (weightedWalshSpectralDensity f w)

/-- The high-frequency tail selected by the unit threshold on the weighted Laplacian eigenvalue. -/
def hypercubeWeightedStokesHighFrequencyTail {n : Nat} (f : Omega.Word n -> Complex)
    (w : Fin n -> Real) : Real :=
  Finset.sum (((Finset.univ : Finset (Fin n)).powerset.filter
      fun I => 1 ≤ |weightedWalshEigenvalue I w|)) (weightedWalshSpectralDensity f w)

/-- Concrete Sobolev-energy spectral package for the weighted hypercube Stokes system: the energy
is written as the weighted Walsh sum, and the high-frequency tail is bounded by the full spectral
energy because every retained summand is nonnegative. -/
def HypercubeWeightedStokesSobolevEnergyLaw {n : Nat} (f : Omega.Word n -> Complex)
    (w : Fin n -> Real) : Prop :=
  hypercubeWeightedStokesDirichletEnergy f w =
      Finset.sum ((Finset.univ : Finset (Fin n)).powerset) (weightedWalshSpectralDensity f w) ∧
    hypercubeWeightedStokesHighFrequencyTail f w ≤ hypercubeWeightedStokesDirichletEnergy f w

lemma weightedWalshSpectralDensity_nonneg {n : Nat} (f : Omega.Word n -> Complex)
    (w : Fin n -> Real) (I : Finset (Fin n)) : 0 ≤ weightedWalshSpectralDensity f w I := by
  unfold weightedWalshSpectralDensity
  exact mul_nonneg (abs_nonneg _) (Complex.normSq_nonneg _)

/-- Paper label: `thm:fold-hypercube-weighted-stokes-sobolev-energy-spectrum`. -/
theorem paper_fold_hypercube_weighted_stokes_sobolev_energy_spectrum {n : Nat}
    (f : Omega.Word n -> Complex) (w : Fin n -> Real) :
    HypercubeWeightedStokesSobolevEnergyLaw f w := by
  refine ⟨rfl, ?_⟩
  unfold hypercubeWeightedStokesHighFrequencyTail hypercubeWeightedStokesDirichletEnergy
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro I _ _
  exact weightedWalshSpectralDensity_nonneg f w I

end

end Omega.SPG
