import Omega.Core.WalshStokes
import Omega.Core.WalshFourier

namespace Omega.SPG

open scoped BigOperators

abbrev BoundaryWords (I : Finset (Fin n)) := Omega.Core.BoundaryWords I
abbrev FlipSubsets (I : Finset (Fin n)) := Omega.Core.DeltaSubsets I

/-- Flip every coordinate in `I`; this is the hypercube face involution used in the
Stokes/Walsh comparison. -/
def hypercubeFlip (I : Finset (Fin n)) (w : Word n) : Word n :=
  Omega.Core.flipSet I w

/-- Iterated discrete difference across the coordinates in `I`. -/
def iteratedDifference (f : (Fin n → Bool) → ℝ) (I : Finset (Fin n)) (w : Fin n → Bool) : ℝ :=
  ∑ J : FlipSubsets I, (-1 : ℝ) ^ J.1.card * f (hypercubeFlip J.1 w)

/-- Boundary sum of the iterated difference over the codimension-`|I|` face where all coordinates
in `I` are set to `false`. -/
def discreteStokesBoundarySum (f : (Fin n → Bool) → ℝ) (I : Finset (Fin n)) : ℝ :=
  ∑ w : BoundaryWords I, iteratedDifference f I w.1

/-- Walsh bias written as the signed sum over the active coordinates from `I`. -/
def walshBias (f : (Fin n → Bool) → ℝ) (I : Finset (Fin n)) : ℝ :=
  ∑ w : Word n, (-1 : ℝ) ^ ((Omega.Core.activeBits I w).card) * f w

/-- Paper label: `thm:spg-walsh-discrete-stokes-holography`. -/
theorem paper_spg_walsh_discrete_stokes_holography
    (n : ℕ) (f : (Fin n → Bool) → ℝ) (I : Finset (Fin n)) :
    walshBias f I = discreteStokesBoundarySum f I := by
  let e : BoundaryWords I × FlipSubsets I ≃ Word n :=
    { toFun := fun p => hypercubeFlip p.2.1 p.1.1
      invFun := fun w =>
        (⟨Omega.Core.clearBits I w, by
            intro i hi
            simp [Omega.Core.clearBits, hi]⟩,
          ⟨Omega.Core.activeBits I w, by
            intro i hi
            exact (Omega.Core.activeBits_mem I w i).mp hi |>.1⟩)
      left_inv := by
        intro p
        rcases p with ⟨w, J⟩
        rcases w with ⟨w, hw⟩
        rcases J with ⟨J, hJ⟩
        apply Prod.ext
        · apply Subtype.ext
          exact Omega.Core.clearBits_flipSet (A := I) (B := J) (w := w) hJ hw
        · apply Subtype.ext
          exact Omega.Core.activeBits_flipSet (A := I) (B := J) (w := w) hJ hw
      right_inv := by
        intro w
        exact Omega.Core.flipSet_activeBits_clearBits I w }
  symm
  unfold discreteStokesBoundarySum iteratedDifference walshBias
  simpa [Fintype.sum_prod_type, Omega.Core.activeBits] using
    (Fintype.sum_equiv e
      (fun p : BoundaryWords I × FlipSubsets I =>
        (-1 : ℝ) ^ p.2.1.card * f (hypercubeFlip p.2.1 p.1.1))
      (fun w : Word n => (-1 : ℝ) ^ (Omega.Core.activeBits I w).card * f w)
      (by
        intro p
        rcases p with ⟨w, J⟩
        rcases w with ⟨w, hw⟩
        rcases J with ⟨J, hJ⟩
        have hactive : Omega.Core.activeBits I (Omega.Core.flipSet J w) = J :=
          Omega.Core.activeBits_flipSet (A := I) (B := J) (w := w) hJ hw
        simp [e, hypercubeFlip, hactive]))

/-- Paper label: `cor:spg-walsh-stokes-sqrt-fiber-holography`. -/
theorem paper_spg_walsh_stokes_sqrt_fiber_holography
    (m : ℕ) (X : Type*) [Fintype X] [DecidableEq X] (f : Omega.Word m → X) (I : Finset (Fin m)) :
    let g : Omega.Word m → ℝ :=
      fun w => Real.sqrt (Fintype.card {w' // f w' = f w} : ℝ)
    Omega.SPG.walshBias g I = Omega.SPG.discreteStokesBoundarySum g I := by
  dsimp
  exact paper_spg_walsh_discrete_stokes_holography m
    (fun w => Real.sqrt (Fintype.card {w' // f w' = f w} : ℝ)) I

/-- Paper label: `cor:spg-walsh-fourier-inversion-completeness`. -/
theorem paper_spg_walsh_fourier_inversion_completeness (f : Omega.Word n → ℤ)
    (w : Omega.Word n) :
    ((2 : ℤ) ^ n) * f w =
      ∑ I : Finset (Fin n), Omega.Core.walshBias f I * Omega.Core.walshChar I w := by
  exact Omega.Core.paper_walsh_fourier_inversion_completeness f w

end Omega.SPG
