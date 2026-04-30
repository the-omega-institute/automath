import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-godel-filament-connected-lie-blindness`. -/
theorem paper_conclusion_godel_filament_connected_lie_blindness
    (Event Filament Solenoid Torus LieChannel : Type*) (X : Event -> Filament)
    (incl : Filament -> Solenoid) (pi0 : Solenoid -> Torus) (zeroTorus : Torus)
    (f : Filament -> LieChannel) (samePrefix : ℕ -> Event -> Event -> Prop)
    (hKilled : ∀ e, pi0 (incl (X e)) = zeroTorus)
    (hFinitePrefix : ∃ n0, ∀ e e', samePrefix n0 e e' -> f (X e) = f (X e')) :
    (∀ e, pi0 (incl (X e)) = zeroTorus) ∧
      ∃ n0, ∀ e e', samePrefix n0 e e' -> f (X e) = f (X e') := by
  exact ⟨hKilled, hFinitePrefix⟩

end Omega.Conclusion
