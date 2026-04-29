import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete affine-transport data for good-prime Hankel stiffness. -/
structure conclusion_goodprime_permanent_hankel_stability_data where
  stiffness : ℕ → ℤ
  k0 : ℕ
  slope : ℤ
  initialZero : stiffness k0 = 0
  slopeZero : slope = 0
  affineTransport : ∀ r : ℕ, stiffness (k0 + r) = stiffness k0 + (r : ℤ) * slope

/-- Permanent stability means every later witness block has zero stiffness. -/
def conclusion_goodprime_permanent_hankel_stability_data.permanentStability
    (D : conclusion_goodprime_permanent_hankel_stability_data) : Prop :=
  ∀ r : ℕ, D.stiffness (D.k0 + r) = 0

/-- Paper label: `cor:conclusion-goodprime-permanent-hankel-stability`. -/
theorem paper_conclusion_goodprime_permanent_hankel_stability
    (D : conclusion_goodprime_permanent_hankel_stability_data) :
    D.permanentStability := by
  intro r
  rw [D.affineTransport r, D.initialZero, D.slopeZero]
  simp

end Omega.Conclusion
