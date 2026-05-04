import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fiber-fusion-dimension-geometry-same-law`. -/
theorem paper_conclusion_fiber_fusion_dimension_geometry_same_law {r : Nat}
    (ell Hdim : Fin r -> Nat) (d : Nat)
    (hH : forall i, Hdim i = Nat.fib (ell i + 2))
    (hd : d = Finset.univ.prod (fun i => Nat.fib (ell i + 2))) :
    Finset.univ.prod Hdim = d := by
  rw [hd]
  exact Finset.prod_congr rfl (by intro i _; exact hH i)

end Omega.Conclusion
