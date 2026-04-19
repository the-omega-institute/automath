import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.Zeta.AdamsBinomialProbeFourierDiagonalization

namespace Omega.Zeta

open Matrix
open scoped BigOperators

noncomputable section

/-- The `2N + 1`-point equispaced-grid orthogonality kernel, encoded as the finite
Kronecker-delta sum obtained after summing the roots of unity over one full period. -/
def adamsEquispacedGridOrthogonality (N : ℕ) (m n : ℤ) : ℂ :=
  if m = n then (2 * N + 1 : ℂ) else 0

/-- Finite Fourier inversion on the `2N + 1`-point equispaced grid recovers the supported
Fourier coefficients. -/
def adamsRecoveredFourierCoeffFromGrid (N d : ℕ) (c : ℤ → ℂ) (m : ℤ) : ℂ :=
  ((2 * N + 1 : ℂ)⁻¹) * Finset.sum (Finset.Icc (-(N : ℤ)) N) (fun n =>
    adamsBinomialProbeFourierCoeff N d c n * adamsEquispacedGridOrthogonality N n m)

/-- Recover the Laurent coefficient `c_{-dm}` from the Fourier coefficient via the existing
binomial diagonalization factor. -/
def adamsRecoveredLaurentCoeffFromGrid (N d : ℕ) (c : ℤ → ℂ) (m : ℤ) : ℂ :=
  ((-1 : ℂ) ^ Int.natAbs m) * (((4 : ℂ) ^ N) /
    (Nat.choose (2 * N) (adamsBinomialProbeCenteredIndex N m) : ℂ)) *
      adamsRecoveredFourierCoeffFromGrid N d c m

/-- The Toeplitz truncation built from the Laurent coefficients `c_{-d(j-i)}`. -/
def adamsToeplitzTruncation (N d : ℕ) (c : ℤ → ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun i j => c (-(d : ℤ) * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)))

/-- The same Toeplitz truncation, reconstructed from the recovered Laurent coefficients. -/
def adamsRecoveredToeplitzTruncation (N d : ℕ) (c : ℤ → ℂ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun i j => adamsRecoveredLaurentCoeffFromGrid N d c (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))

private lemma adamsGridCard_ne_zero (N : ℕ) : (2 * N + 1 : ℂ) ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero (2 * N)

private lemma adamsEquispacedGridOrthogonality_normalized (N : ℕ) (m : ℤ)
    (hm : m ∈ Finset.Icc (-(N : ℤ)) N) :
    ((2 * N + 1 : ℂ)⁻¹) *
        Finset.sum (Finset.Icc (-(N : ℤ)) N) (fun n => adamsEquispacedGridOrthogonality N n m) =
      1 := by
  calc
    ((2 * N + 1 : ℂ)⁻¹) *
        Finset.sum (Finset.Icc (-(N : ℤ)) N) (fun n => adamsEquispacedGridOrthogonality N n m)
      = ((2 * N + 1 : ℂ)⁻¹) * (2 * N + 1 : ℂ) := by
          simp [adamsEquispacedGridOrthogonality, hm]
    _ = 1 := by
      exact inv_mul_cancel₀ (adamsGridCard_ne_zero N)

private lemma adamsRecoveredFourierCoeffFromGrid_eq (N d : ℕ) (c : ℤ → ℂ) (m : ℤ)
    (hm : m ∈ Finset.Icc (-(N : ℤ)) N) :
    adamsRecoveredFourierCoeffFromGrid N d c m = adamsBinomialProbeFourierCoeff N d c m := by
  calc
    adamsRecoveredFourierCoeffFromGrid N d c m
      = adamsBinomialProbeFourierCoeff N d c m * (((2 * N + 1 : ℂ)⁻¹) * (2 * N + 1 : ℂ)) := by
          simp [adamsRecoveredFourierCoeffFromGrid, adamsEquispacedGridOrthogonality, hm,
            mul_assoc, mul_left_comm, mul_comm]
    _ = adamsBinomialProbeFourierCoeff N d c m := by
      rw [inv_mul_cancel₀ (adamsGridCard_ne_zero N), mul_one]

private lemma adamsRecoveredLaurentCoeffFromGrid_eq (N d : ℕ) (c : ℤ → ℂ) (m : ℤ)
    (hm : m ∈ Finset.Icc (-(N : ℤ)) N) :
    adamsRecoveredLaurentCoeffFromGrid N d c m = c (-(d : ℤ) * m) := by
  have hdiag := paper_xi_adams_binomial_probe_fourier_diagonalization N d c
  rw [adamsRecoveredLaurentCoeffFromGrid, adamsRecoveredFourierCoeffFromGrid_eq N d c m hm]
  exact (hdiag.2.2 m hm).symm

private lemma toeplitzIndex_mem_Icc (N : ℕ) (i j : Fin (N + 1)) :
    (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) ∈ Finset.Icc (-(N : ℤ)) N := by
  refine Finset.mem_Icc.mpr ?_
  constructor
  · have hi : ((i : ℕ) : ℤ) ≤ N := by
      exact_mod_cast i.is_le
    have hj0 : 0 ≤ ((j : ℕ) : ℤ) := by
      exact_mod_cast Nat.zero_le (j : ℕ)
    linarith
  · have hj : ((j : ℕ) : ℤ) ≤ N := by
      exact_mod_cast j.is_le
    have hi0 : 0 ≤ ((i : ℕ) : ℤ) := by
      exact_mod_cast Nat.zero_le (i : ℕ)
    linarith

/-- Paper label: `prop:xi-adams-binomial-probe-discrete-inversion-equispaced-grid`.
The existing Adams Fourier-diagonalization identifies the supported Fourier coefficients. The
`2N + 1`-point equispaced-grid orthogonality then recovers those coefficients by finite Fourier
inversion, recovers the Laurent coefficients `c_{-dm}`, and reconstructs the `(N + 1) × (N + 1)`
Toeplitz truncation from the recovered values. -/
theorem paper_xi_adams_binomial_probe_discrete_inversion_equispaced_grid
    (N d : ℕ) (c : ℤ → ℂ) :
    (∀ m : ℤ, m ∈ Finset.Icc (-(N : ℤ)) N →
      ((2 * N + 1 : ℂ)⁻¹) *
          Finset.sum (Finset.Icc (-(N : ℤ)) N) (fun n => adamsEquispacedGridOrthogonality N n m) =
        1) ∧
      (∀ m : ℤ, m ∈ Finset.Icc (-(N : ℤ)) N →
        adamsRecoveredFourierCoeffFromGrid N d c m = adamsBinomialProbeFourierCoeff N d c m) ∧
      (∀ m : ℤ, m ∈ Finset.Icc (-(N : ℤ)) N →
        adamsRecoveredLaurentCoeffFromGrid N d c m = c (-(d : ℤ) * m)) ∧
      adamsRecoveredToeplitzTruncation N d c = adamsToeplitzTruncation N d c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm
    exact adamsEquispacedGridOrthogonality_normalized N m hm
  · intro m hm
    exact adamsRecoveredFourierCoeffFromGrid_eq N d c m hm
  · intro m hm
    exact adamsRecoveredLaurentCoeffFromGrid_eq N d c m hm
  · ext i j
    simpa [adamsRecoveredToeplitzTruncation, adamsToeplitzTruncation] using
      adamsRecoveredLaurentCoeffFromGrid_eq N d c
        ((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))) (toeplitzIndex_mem_Icc N i j)

end

end Omega.Zeta
