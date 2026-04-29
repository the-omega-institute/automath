import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `cor:conclusion-centered-trigonal-observable-sign-shadow-orthogonality`. -/
theorem paper_conclusion_centered_trigonal_observable_sign_shadow_orthogonality
    {eps tau : Type*} [Fintype eps] [Fintype tau] (density : eps -> Complex)
    (cond : eps -> tau -> Complex) (g : eps -> Complex) (f : tau -> Complex)
    (hzero : forall e : eps, (Finset.univ.sum fun t : tau => cond e t * f t) = 0) :
    (Finset.univ.sum fun e : eps =>
      density e * g e * (Finset.univ.sum fun t : tau => cond e t * f t)) = 0 := by
  simp [hzero]

end Omega.Conclusion
