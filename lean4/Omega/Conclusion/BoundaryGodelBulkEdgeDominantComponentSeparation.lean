import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-boundary-godel-bulk-edge-dominant-component-separation`. -/
theorem paper_conclusion_boundary_godel_bulk_edge_dominant_component_separation
    {Obj α : Type} [LinearOrder α]
    (dG dBoundary gamma : Obj → α) (union : Obj → Obj → Obj) (A B : Obj)
    (bulk_union : dG (union A B) = max (dG A) (dG B))
    (boundary_eq_gamma : dBoundary (union A B) = gamma (union A B))
    (gamma_union : gamma (union A B) = max (gamma A) (gamma B))
    (hbulk : dG A < dG B) (hgamma : gamma B < gamma A) :
    dG (union A B) = dG B ∧ dBoundary (union A B) = gamma A := by
  constructor
  · calc
      dG (union A B) = max (dG A) (dG B) := bulk_union
      _ = dG B := max_eq_right (le_of_lt hbulk)
  · calc
      dBoundary (union A B) = gamma (union A B) := boundary_eq_gamma
      _ = max (gamma A) (gamma B) := gamma_union
      _ = gamma A := max_eq_left (le_of_lt hgamma)

end Omega.Conclusion
