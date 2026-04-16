import Mathlib.Tactic

namespace Omega.SPG

/-- Abstract paper-facing corollary: if the boundary Gödel integer determines the finite
moment box, and the finite moment box is already complete, then the boundary Gödel code is
injective.
    cor:spg-boundary-godel-finite-moment-completeness -/
theorem paper_spg_boundary_godel_finite_moment_completeness {U H M : Type}
    (encode : U → H) (momentBox : U → M)
    (hReadout : ∀ u v, encode u = encode v → momentBox u = momentBox v)
    (hComplete : Function.Injective momentBox) : Function.Injective encode := by
  intro u v hEq
  exact hComplete (hReadout u v hEq)

end Omega.SPG
