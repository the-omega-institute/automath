import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-sqrt5-axis-leyang-cubic-linear-disjoint`. -/
theorem paper_xi_sqrt5_axis_leyang_cubic_linear_disjoint
    (intersectionTrivial linearlyDisjoint degreeProduct galoisProduct : Prop)
    (h_intersection : intersectionTrivial) (h_linear : intersectionTrivial -> linearlyDisjoint)
    (h_degree : linearlyDisjoint -> degreeProduct) (h_galois : linearlyDisjoint -> galoisProduct) :
    intersectionTrivial ∧ linearlyDisjoint ∧ degreeProduct ∧ galoisProduct := by
  have h_linearlyDisjoint : linearlyDisjoint := h_linear h_intersection
  exact ⟨h_intersection, h_linearlyDisjoint, h_degree h_linearlyDisjoint,
    h_galois h_linearlyDisjoint⟩

end Omega.Zeta
