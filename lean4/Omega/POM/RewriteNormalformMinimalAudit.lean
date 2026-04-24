import Mathlib.Tactic

namespace Omega.POM

/-- The canonical normal form minimizes the audit gate count in its equivalence class, and equality
of gate counts forces the representative to already be the normal form.
    cor:pom-rewrite-normalform-minimal-audit -/
theorem paper_pom_rewrite_normalform_minimal_audit {alpha : Type} (N : alpha -> alpha)
    (eqv : alpha -> alpha -> Prop) (g : alpha -> Nat)
    (hmin : ∀ W W', eqv W' W -> g (N W) <= g W')
    (heq : ∀ W W', eqv W' W -> g W' = g (N W) -> W' = N W) :
    ∀ W W', eqv W' W -> g (N W) <= g W' ∧ (g W' = g (N W) -> W' = N W) := by
  intro W W' hEqv
  refine ⟨hmin W W' hEqv, ?_⟩
  intro hCount
  exact heq W W' hEqv hCount

end Omega.POM
