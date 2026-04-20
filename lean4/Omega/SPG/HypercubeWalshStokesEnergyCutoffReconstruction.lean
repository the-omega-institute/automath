import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
import Omega.SPG.HypercubeWeightedStokesSobolevEnergySpectrum

namespace Omega.SPG

open scoped BigOperators

noncomputable section

/-- The retained Walsh coefficient after cutting off all modes above `Λ`. -/
def hypercubeWalshCutoffProjectorCoeff {n : Nat} (f : Omega.Word n → Complex) (w : Fin n → Real)
    (Λ : Real) (I : Finset (Fin n)) : Complex :=
  if |weightedWalshEigenvalue I w| ≤ Λ then weightedWalshFourierCoeff f I else 0

/-- The omitted Walsh coefficient above the energy cutoff `Λ`. -/
def hypercubeWalshCutoffRemainderCoeff {n : Nat} (f : Omega.Word n → Complex) (w : Fin n → Real)
    (Λ : Real) (I : Finset (Fin n)) : Complex :=
  if |weightedWalshEigenvalue I w| ≤ Λ then 0 else weightedWalshFourierCoeff f I

/-- The Walsh modes omitted by the energy cutoff `Λ`. -/
def hypercubeWalshCutoffOmittedModes {n : Nat} (w : Fin n → Real) (Λ : Real) :
    Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powerset).filter fun I => Λ < |weightedWalshEigenvalue I w|

/-- Squared `L²` tail norm of the omitted Walsh spectrum in coefficient form. -/
def hypercubeWalshCutoffTailNormSq {n : Nat} (f : Omega.Word n → Complex) (w : Fin n → Real)
    (Λ : Real) : Real :=
  Finset.sum (hypercubeWalshCutoffOmittedModes w Λ) fun I =>
    Complex.normSq (hypercubeWalshCutoffRemainderCoeff f w Λ I)

/-- Concrete cutoff-reconstruction package: the retained and omitted Walsh coefficients split the
full spectrum, and the omitted tail is bounded by the weighted Walsh-Stokes Dirichlet energy. -/
def hypercubeWalshStokesEnergyCutoffReconstructionStatement : Prop :=
  ∀ {n : Nat} (f : Omega.Word n → Complex) (w : Fin n → Real) (Λ : Real),
    0 < Λ →
      (∀ I : Finset (Fin n),
        hypercubeWalshCutoffProjectorCoeff f w Λ I +
          hypercubeWalshCutoffRemainderCoeff f w Λ I =
          weightedWalshFourierCoeff f I) ∧
      hypercubeWalshCutoffTailNormSq f w Λ ≤
        (1 / Λ) * hypercubeWeightedStokesDirichletEnergy f w

private lemma hypercubeWalshCutoff_mode_bound {n : Nat} (f : Omega.Word n → Complex)
    (w : Fin n → Real) {Λ : Real} (hΛ : 0 < Λ) (I : Finset (Fin n))
    (hI : Λ ≤ |weightedWalshEigenvalue I w|) :
    Complex.normSq (weightedWalshFourierCoeff f I) ≤
      (1 / Λ) * weightedWalshSpectralDensity f w I := by
  have hnorm : 0 ≤ Complex.normSq (weightedWalshFourierCoeff f I) := Complex.normSq_nonneg _
  have hfactor :
      1 ≤ |weightedWalshEigenvalue I w| * (1 / Λ) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hI (one_div_nonneg.mpr (le_of_lt hΛ))
    have hone : Λ * (1 / Λ) = (1 : Real) := by
      field_simp [hΛ.ne']
    calc
      (1 : Real) = Λ * (1 / Λ) := by symm; exact hone
      _ ≤ |weightedWalshEigenvalue I w| * (1 / Λ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hbound :
      Complex.normSq (weightedWalshFourierCoeff f I) ≤
        (|weightedWalshEigenvalue I w| * (1 / Λ)) *
          Complex.normSq (weightedWalshFourierCoeff f I) := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hfactor hnorm
  calc
    Complex.normSq (weightedWalshFourierCoeff f I) ≤
        (|weightedWalshEigenvalue I w| * (1 / Λ)) *
          Complex.normSq (weightedWalshFourierCoeff f I) := hbound
    _ = (1 / Λ) * (|weightedWalshEigenvalue I w| *
        Complex.normSq (weightedWalshFourierCoeff f I)) := by ring
    _ = (1 / Λ) * weightedWalshSpectralDensity f w I := by
        rfl

/-- Paper label: `thm:fold-hypercube-walsh-stokes-energy-cutoff-reconstruction`. -/
theorem paper_fold_hypercube_walsh_stokes_energy_cutoff_reconstruction :
    hypercubeWalshStokesEnergyCutoffReconstructionStatement := by
  intro n f w Λ hΛ
  refine ⟨?_, ?_⟩
  · intro I
    by_cases hI : |weightedWalshEigenvalue I w| ≤ Λ
    · simp [hypercubeWalshCutoffProjectorCoeff, hypercubeWalshCutoffRemainderCoeff, hI]
    · simp [hypercubeWalshCutoffProjectorCoeff, hypercubeWalshCutoffRemainderCoeff, hI]
  · have htail :
        hypercubeWalshCutoffTailNormSq f w Λ ≤
          Finset.sum (hypercubeWalshCutoffOmittedModes w Λ) fun I =>
            (1 / Λ) * weightedWalshSpectralDensity f w I := by
      unfold hypercubeWalshCutoffTailNormSq
      refine Finset.sum_le_sum ?_
      intro I hI
      have hI' : Λ < |weightedWalshEigenvalue I w| := by
        simpa [hypercubeWalshCutoffOmittedModes] using (Finset.mem_filter.mp hI).2
      simp [hypercubeWalshCutoffRemainderCoeff, not_le_of_gt hI']
      simpa [one_div] using hypercubeWalshCutoff_mode_bound f w hΛ I (le_of_lt hI')
    have hsubset :
        (Finset.sum (hypercubeWalshCutoffOmittedModes w Λ) fun I =>
          (1 / Λ) * weightedWalshSpectralDensity f w I) ≤
          Finset.sum ((Finset.univ : Finset (Fin n)).powerset) fun I =>
            (1 / Λ) * weightedWalshSpectralDensity f w I := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro I hI
        exact (Finset.mem_filter.mp hI).1
      intro I _ _
      exact mul_nonneg (one_div_nonneg.mpr (le_of_lt hΛ)) (weightedWalshSpectralDensity_nonneg f w I)
    calc
      hypercubeWalshCutoffTailNormSq f w Λ ≤
          Finset.sum (hypercubeWalshCutoffOmittedModes w Λ) fun I =>
            (1 / Λ) * weightedWalshSpectralDensity f w I := htail
      _ ≤ Finset.sum ((Finset.univ : Finset (Fin n)).powerset) fun I =>
            (1 / Λ) * weightedWalshSpectralDensity f w I := hsubset
      _ = (1 / Λ) * hypercubeWeightedStokesDirichletEnergy f w := by
          simp [hypercubeWeightedStokesDirichletEnergy, Finset.mul_sum]

end

end Omega.SPG
