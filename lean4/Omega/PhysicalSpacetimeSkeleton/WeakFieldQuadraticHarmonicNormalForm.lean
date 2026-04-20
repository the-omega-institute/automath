import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton

/-- A weak-field potential with constant source splits into the normalized quadratic model plus a
harmonic correction.  This is the linear-algebraic normal-form version of the weak-field argument.
    thm:physical-spacetime-weak-field-quadratic-harmonic-normal-form -/
theorem paper_physical_spacetime_weak_field_quadratic_harmonic_normal_form
    (Delta : (Fin 3 → Real) →ₗ[Real] Real) (phi q : Fin 3 → Real) (sigma L : Real)
    (hq : Delta q = sigma * L) (hphi : Delta phi = sigma * L) :
    ∃ h : Fin 3 → Real, phi = q + h ∧ Delta h = 0 := by
  refine ⟨phi - q, ?_, ?_⟩
  · ext i
    simp
  · rw [LinearMap.map_sub, hphi, hq, sub_self]

end Omega.PhysicalSpacetimeSkeleton
