import Mathlib.Tactic

namespace Omega.Zeta

/-- Cross-multiplication for a fractional linear parameter recovers equality of parameters when
the determinant is nonzero.
    thm:xi-hankel-fiber-mobius-rigidity -/
theorem paper_xi_hankel_fiber_mobius_rigidity {K : Type*} [Field K] (A B C D x x' : K)
    (hdet : A * D - B * C ≠ 0) (hx : C * x + D ≠ 0) (hx' : C * x' + D ≠ 0)
    (heq : (A * x + B) / (C * x + D) = (A * x' + B) / (C * x' + D)) :
    x = x' := by
  have hcross :
      (A * x + B) * (C * x' + D) = (A * x' + B) * (C * x + D) := by
    exact (div_eq_div_iff hx hx').mp heq
  have hprod : (A * D - B * C) * (x - x') = 0 := by
    have hsub :
        (A * x + B) * (C * x' + D) - (A * x' + B) * (C * x + D) = 0 :=
      sub_eq_zero.mpr hcross
    rw [show (A * x + B) * (C * x' + D) - (A * x' + B) * (C * x + D) =
        (A * D - B * C) * (x - x') by ring] at hsub
    exact hsub
  have hxsub : x - x' = 0 := (mul_eq_zero.mp hprod).resolve_left hdet
  exact sub_eq_zero.mp hxsub

end Omega.Zeta
