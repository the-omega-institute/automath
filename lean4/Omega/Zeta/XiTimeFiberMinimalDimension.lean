import Mathlib
import Omega.Zeta.LayeredPrimesliceLocalAlphabetFibermax

namespace Omega.Zeta

/-- A reversible time lift can separate every fiber by tagging its points with distinct time
register values. -/
def XiTimeRegisterRealization {Ω X : Type*} (Fold : Ω → X) (T : ℕ) : Prop :=
  ∃ q : Ω → Fin T, FiberwiseInjective Fold q

/-- The auxiliary time register must have size at least the maximal fiber size, and `Fin D`
realizes that lower bound exactly.
    thm:xi-time-fiber-minimal-dimension -/
theorem paper_xi_time_fiber_minimal_dimension
    {Ω X : Type*} [Fintype Ω] (Fold : Ω → X) (D T : ℕ)
    (hmax : ∀ x, Nat.card (LayerFiber Fold x) ≤ D)
    (hwit : ∃ x, Nat.card (LayerFiber Fold x) = D) :
    (XiTimeRegisterRealization Fold T ↔ D ≤ T) ∧ XiTimeRegisterRealization Fold D := by
  constructor
  · simpa [XiTimeRegisterRealization] using
      (paper_xi_layered_primeslice_local_alphabet_fibermax
        (π := Fold) (Λ := Fin T) (B := D) hmax hwit)
  · have hD : D ≤ Fintype.card (Fin D) := by simp
    exact
      (paper_xi_layered_primeslice_local_alphabet_fibermax
        (π := Fold) (Λ := Fin D) (B := D) hmax hwit).2 hD

end Omega.Zeta
