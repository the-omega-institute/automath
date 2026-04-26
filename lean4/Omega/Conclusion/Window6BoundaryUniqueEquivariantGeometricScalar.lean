import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-boundary-unique-equivariant-geometric-scalar`. -/
theorem paper_conclusion_window6_boundary_unique_equivariant_geometric_scalar
    (a b c : ZMod 2) (hcycle : a = b ∧ b = c) :
    (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 1 ∧ b = 1 ∧ c = 1) := by
  rcases hcycle with ⟨hab, hbc⟩
  subst b
  subst c
  fin_cases a <;> simp

end Omega.Conclusion
