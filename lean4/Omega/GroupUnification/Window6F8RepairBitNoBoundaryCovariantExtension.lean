import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryParityNotMeasurableFromF8

namespace Omega.GroupUnification

open Omega.Conclusion

/-- Boundary-sheet involution on the three audited two-point fibers. -/
def window6BoundaryFiberFlip (x : Window6BoundaryPoint) : Window6BoundaryPoint :=
  (x.1, !x.2)

/-- A boundary bit is covariant when it flips under the fiber involution on every boundary sheet.
    This is the Boolean version of the paper's `χ(τ_w η) = 1 - χ(η)` rule. -/
def window6BoundaryCovariant (χ : Window6BoundaryPoint → Bool) : Prop :=
  ∀ x : Window6BoundaryPoint, χ (window6BoundaryFiberFlip x) = !χ x

/-- Paper-facing boundary obstruction: the `F₈` repair bit is identically `0` on the audited
boundary sector, so no boundary-covariant extension can agree with it there.
    thm:window6-f8-repair-bit-no-boundary-covariant-extension -/
theorem paper_window6_f8_repair_bit_no_boundary_covariant_extension :
    (∀ x : Window6BoundaryPoint, window6F8RepairBit x = false) ∧
      ¬ ∃ χ : Window6BoundaryPoint → Bool,
        (∀ x : Window6BoundaryPoint, χ x = window6F8RepairBit x) ∧
          window6BoundaryCovariant χ := by
  refine ⟨?_, ?_⟩
  · intro x
    rfl
  · rintro ⟨χ, hχ, hcov⟩
    have hflip := hcov ((0 : Fin 3), false)
    have hleft : χ ((0 : Fin 3), false) = false := by
      simpa [window6F8RepairBit] using hχ ((0 : Fin 3), false)
    have hright : χ ((0 : Fin 3), true) = false := by
      simpa [window6F8RepairBit] using hχ ((0 : Fin 3), true)
    rw [window6BoundaryFiberFlip] at hflip
    simp only [Bool.not_false] at hflip
    rw [hright, hleft] at hflip
    simp at hflip

end Omega.GroupUnification
