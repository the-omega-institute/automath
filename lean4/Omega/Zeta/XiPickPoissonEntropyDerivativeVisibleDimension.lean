import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-pick-poisson-entropy-derivative-visible-dimension`. Once the determinant
scales by `m^{-κ}` and `Sgen` is defined as `-log detP`, the entropy profile is affine in
`log m`. -/
theorem paper_xi_pick_poisson_entropy_derivative_visible_dimension (kappa : Nat)
    (detP Sgen : Real -> Real) (hpos : 0 < detP 1)
    (hdet : ∀ m : Real, 0 < m -> detP m = detP 1 / m^kappa)
    (hSgen : ∀ m : Real, 0 < m -> Sgen m = -Real.log (detP m)) :
    ∀ m : Real, 0 < m -> Sgen m = Sgen 1 + (kappa : Real) * Real.log m := by
  intro m hm
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have hpow_ne : (m ^ kappa : Real) ≠ 0 := pow_ne_zero kappa hm_ne
  rw [hSgen m hm, hSgen 1 zero_lt_one, hdet m hm]
  rw [Real.log_div (ne_of_gt hpos) hpow_ne]
  rw [show Real.log (m ^ kappa) = (kappa : Real) * Real.log m by
    rw [← Real.rpow_natCast]
    rw [Real.log_rpow hm]]
  ring

end Omega.Zeta
