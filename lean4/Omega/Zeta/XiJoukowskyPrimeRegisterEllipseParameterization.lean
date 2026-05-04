import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `cor:xi-joukowsky-prime-register-ellipse-parameterization`. -/
theorem paper_xi_joukowsky_prime_register_ellipse_parameterization {Register : Type}
    (sqrtN logN a b shift : Register → ℝ)
    (hA : ∀ r, a r = sqrtN r + (sqrtN r)⁻¹)
    (hB : ∀ r, b r = sqrtN r - (sqrtN r)⁻¹)
    (hShift : ∀ r, shift r = (1 / 2 : ℝ) * logN r) :
    ∀ r,
      a r = sqrtN r + (sqrtN r)⁻¹ ∧
        b r = sqrtN r - (sqrtN r)⁻¹ ∧ shift r = (1 / 2 : ℝ) * logN r := by
  intro r
  exact ⟨hA r, hB r, hShift r⟩

end Omega.Zeta
