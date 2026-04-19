import Mathlib.Tactic

namespace Omega.GU

/-- Prime-`23` spectral/response fingerprint: the same prime appears both in the discriminant and
as a nontrivial torsion prime of the response group. -/
theorem paper_window6_prime23_spectral_response {G : Type*} [AddCommGroup G] {Δ : ℤ}
    (hdisc23 : 23 ∣ Δ) (h23tors : ∃ g : G, g ≠ 0 ∧ 23 • g = 0) :
    23 ∣ Δ ∧ ∃ g : G, g ≠ 0 ∧ 23 • g = 0 := by
  exact ⟨hdisc23, h23tors⟩

end Omega.GU
