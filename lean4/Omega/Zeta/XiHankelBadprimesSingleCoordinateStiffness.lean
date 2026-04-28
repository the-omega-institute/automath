import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-hankel-badprimes-single-coordinate-stiffness`. -/
theorem paper_xi_hankel_badprimes_single_coordinate_stiffness (u detH : ℤ)
    (vp : ℕ → ℤ → ℕ) (hcoord : u = detH) :
    (∀ p : ℕ, ((p : ℤ) ∣ u ↔ (p : ℤ) ∣ detH)) ∧
      (∀ p : ℕ, vp p u = vp p detH) := by
  subst hcoord
  exact ⟨fun _ => Iff.rfl, fun _ => rfl⟩

end Omega.Zeta
