import Mathlib.Tactic

namespace Omega.GroupUnification

/-- Explicit nonzero directions realized by three window-6 two-point fibers. -/
abbrev DirectionVector := ℤ × ℤ

def window6DirA : DirectionVector := (1, 0)
def window6DirB : DirectionVector := (1, 1)
def window6DirC : DirectionVector := (2, 1)

/-- A linear-kernel model would force every two-point fiber to share one common direction. -/
def linearKernelModel : Prop :=
  ∃ d : DirectionVector, window6DirA = d ∧ window6DirB = d ∧ window6DirC = d

/-- The three explicit two-point fibers carry pairwise distinct directions. -/
def threeDistinctTwoPointFiberDirections : Prop :=
  window6DirA ≠ window6DirB ∧ window6DirA ≠ window6DirC ∧ window6DirB ≠ window6DirC

/-- Three distinct two-point fiber directions obstruct any single linear-kernel direction.
    thm:window6-direction-spectrum-linear-kernel-obstruction -/
theorem paper_window6_direction_spectrum_linear_kernel_obstruction :
    threeDistinctTwoPointFiberDirections -> ¬ linearKernelModel := by
  intro hDistinct hKernel
  rcases hDistinct with ⟨hAB, -, -⟩
  rcases hKernel with ⟨d, hA, hB, _⟩
  apply hAB
  calc
    window6DirA = d := hA
    _ = window6DirB := hB.symm

end Omega.GroupUnification
