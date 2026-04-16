import Omega.Core.WalshStokes
import Mathlib.Tactic

namespace Omega.GU

open scoped BigOperators

/-- The Walsh character detecting whether the two affine-involution coordinates
    agree. It is `1` on equal bits and `-1` on unequal bits. -/
def affineInvolutionCharacter (i j : Fin n) (w : Omega.Word n) : ℤ :=
  if w i = w j then 1 else -1

/-- The fixed-point indicator for the affine involution exchanging `i` and `j`
    and flipping both bits. Fixed points are exactly the words with `w i ≠ w j`. -/
def affineInvolutionFixedpointIndicator (i j : Fin n) (w : Omega.Word n) : ℤ :=
  if w i = w j then 0 else 1

/-- Pointwise fixed-point indicator written as `(1 - χ)/2`. -/
theorem affineInvolutionFixedpointIndicator_eq_half_gap (i j : Fin n) (w : Omega.Word n) :
    affineInvolutionFixedpointIndicator i j w = (1 - affineInvolutionCharacter i j w) / 2 := by
  by_cases h : w i = w j <;> simp [affineInvolutionFixedpointIndicator, affineInvolutionCharacter, h]

/-- Clearing the denominator gives an additive identity suitable for summing over
    invariant subsets or fibers. -/
theorem two_mul_affineInvolutionFixedpointIndicator (i j : Fin n) (w : Omega.Word n) :
    2 * affineInvolutionFixedpointIndicator i j w = 1 - affineInvolutionCharacter i j w := by
  by_cases h : w i = w j <;> simp [affineInvolutionFixedpointIndicator, affineInvolutionCharacter, h]

/-- Summed fixed-point count on a finite invariant subset or fiber. -/
theorem affineInvolutionFixedpointCount_double (i j : Fin n) (B : Finset (Omega.Word n)) :
    2 * Finset.sum B (fun w => affineInvolutionFixedpointIndicator i j w) =
      (B.card : ℤ) - Finset.sum B (fun w => affineInvolutionCharacter i j w) := by
  calc
    2 * Finset.sum B (fun w => affineInvolutionFixedpointIndicator i j w)
        = Finset.sum B (fun w => 2 * affineInvolutionFixedpointIndicator i j w) := by
            rw [Finset.mul_sum]
    _ = Finset.sum B (fun w => 1 - affineInvolutionCharacter i j w) := by
          refine Finset.sum_congr rfl ?_
          intro w hw
          simp [two_mul_affineInvolutionFixedpointIndicator]
    _ = Finset.sum B (fun _w => (1 : ℤ)) - Finset.sum B (fun w => affineInvolutionCharacter i j w) := by
          rw [Finset.sum_sub_distrib]
    _ = (B.card : ℤ) - Finset.sum B (fun w => affineInvolutionCharacter i j w) := by
          simp

/-- The `σ_geo = σ_{1,5}` specialization uses the existing Walsh-Stokes
    boundary-readout formula on the coordinate set `{1,5}`. In Lean's
    zero-based indexing this is `{0,4}` on `Fin 6`. -/
theorem sigmaGeo_boundary_readout :
    Omega.Core.walshFlux ({(0 : Fin 6), (4 : Fin 6)} : Finset (Fin 6))
        (affineInvolutionCharacter 0 4) =
      ∑ w : Omega.Word 6,
        (-1 : ℤ) ^
            ((({(0 : Fin 6), (4 : Fin 6)} : Finset (Fin 6)).filter fun i => w i = true).card) *
          affineInvolutionCharacter 0 4 w := by
  simpa using Omega.Core.walshStokes_finset ({(0 : Fin 6), (4 : Fin 6)} : Finset (Fin 6))
    (affineInvolutionCharacter 0 4)

/-- Paper-facing fixed-point/flux package for the terminal affine involution. -/
theorem paper_terminal_hypercube_affine_involution_fixedpoint_gauss_stokes :
    (∀ (n : ℕ) (i j : Fin n) (w : Omega.Word n),
      affineInvolutionFixedpointIndicator i j w = (1 - affineInvolutionCharacter i j w) / 2) ∧
      (∀ B : Finset (Omega.Word 6),
        2 * Finset.sum B (fun w => affineInvolutionFixedpointIndicator 0 4 w) =
          (B.card : ℤ) - Finset.sum B (fun w => affineInvolutionCharacter 0 4 w)) ∧
      Omega.Core.walshFlux ({(0 : Fin 6), (4 : Fin 6)} : Finset (Fin 6))
          (affineInvolutionCharacter 0 4) =
        ∑ w : Omega.Word 6,
          (-1 : ℤ) ^
              ((({(0 : Fin 6), (4 : Fin 6)} : Finset (Fin 6)).filter fun i => w i = true).card) *
            affineInvolutionCharacter 0 4 w := by
  exact ⟨fun n i j w => affineInvolutionFixedpointIndicator_eq_half_gap i j w,
    affineInvolutionFixedpointCount_double 0 4, sigmaGeo_boundary_readout⟩

end Omega.GU
