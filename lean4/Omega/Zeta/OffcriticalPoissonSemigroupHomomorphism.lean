import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-offcritical-poisson-semigroup-homomorphism`. -/
theorem paper_xi_offcritical_poisson_semigroup_homomorphism {Scale Field : Type*} [Add Scale]
    (P : Scale → Field → Field) (G : Scale → Field) (G0 : Field)
    (hP : ∀ s t f, P s (P t f) = P (t + s) f) (hG : ∀ t, G t = P t G0) :
    ∀ s t, G (t + s) = P s (G t) := by
  intro s t
  rw [hG (t + s), hG t, hP]

end Omega.Zeta
