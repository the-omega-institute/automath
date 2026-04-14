import Mathlib.Tactic

namespace Omega.SPG

/-- Paper-facing kernel-triviality criterion for the top boundary map on a dyadic cubical complex.
    thm:spg-dyadic-cubical-boundary-injective -/
theorem paper_spg_dyadic_cubical_boundary_injective
    {Cn Cn1 : Type*} [AddGroup Cn] [AddGroup Cn1]
    (boundary : Cn → Cn1)
    (hsub : ∀ u v, boundary (u - v) = boundary u - boundary v)
    (hker : ∀ u, boundary u = 0 → u = 0) :
    Function.Injective boundary := by
  intro u v huv
  have huv0 : boundary (u - v) = 0 := by
    rw [hsub u v, huv, sub_self]
  have hdiff : u - v = 0 := hker (u - v) huv0
  exact sub_eq_zero.mp hdiff

end Omega.SPG
