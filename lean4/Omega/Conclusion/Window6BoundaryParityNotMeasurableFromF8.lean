import Mathlib.Tactic

namespace Omega.Conclusion

/-- The three boundary fibers, each with two sheets. -/
abbrev Window6BoundaryPoint := Fin 3 × Bool

/-- The boundary-fiber index. -/
def window6BoundaryFiberIndex (x : Window6BoundaryPoint) : Fin 3 :=
  x.1

/-- The `F₈` repair bit restricted to the boundary sector; the paper input is that it is constant
    on each boundary two-point fiber, and we package that boundary restriction as the constant
    boundary readout. -/
def window6F8RepairBit (_x : Window6BoundaryPoint) : Bool :=
  false

/-- Canonical boundary parity is the sheet parity on each boundary two-point fiber. -/
def window6CanonicalBoundaryParity (x : Window6BoundaryPoint) : Bool :=
  x.2

/-- Finite-fiber version of measurability from the repair bit: the function factors through the
    boundary restriction of the repair-bit channel. -/
def window6BoundaryMeasurableFromF8 (g : Window6BoundaryPoint → Bool) : Prop :=
  ∃ h : Bool → Bool, ∀ x, g x = h (window6F8RepairBit x)

/-- Paper-facing obstruction: the boundary repair bit is fiberwise constant, canonical parity is
    complementary on each two-point boundary fiber, so canonical parity cannot factor through the
    repair-bit channel.
    thm:conclusion-window6-boundary-parity-not-measurable-from-f8 -/
theorem paper_conclusion_window6_boundary_parity_not_measurable_from_f8 :
    (∀ x y : Window6BoundaryPoint,
      window6BoundaryFiberIndex x = window6BoundaryFiberIndex y →
        window6F8RepairBit x = window6F8RepairBit y) ∧
    (∀ i : Fin 3,
      window6CanonicalBoundaryParity (i, false) ≠ window6CanonicalBoundaryParity (i, true)) ∧
    ¬ window6BoundaryMeasurableFromF8 window6CanonicalBoundaryParity ∧
    ¬ ∃ identify : Bool → Bool, ∀ x : Window6BoundaryPoint,
      identify (window6F8RepairBit x) = window6CanonicalBoundaryParity x := by
  have hnot :
      ¬ window6BoundaryMeasurableFromF8 window6CanonicalBoundaryParity := by
    intro hmeas
    rcases hmeas with ⟨h, hh⟩
    have h0 : h false = false := by
      simpa [window6CanonicalBoundaryParity, window6F8RepairBit] using
        (hh ((0 : Fin 3), false)).symm
    have h1 : h false = true := by
      simpa [window6CanonicalBoundaryParity, window6F8RepairBit] using
        (hh ((0 : Fin 3), true)).symm
    exact Bool.false_ne_true (h0.symm.trans h1)
  refine ⟨?_, ?_, hnot, ?_⟩
  · intro x y _hxy
    rfl
  · intro i
    simp [window6CanonicalBoundaryParity]
  · intro hident
    apply hnot
    rcases hident with ⟨identify, hidentify⟩
    exact ⟨identify, fun x => by simpa using (hidentify x).symm⟩

end Omega.Conclusion
