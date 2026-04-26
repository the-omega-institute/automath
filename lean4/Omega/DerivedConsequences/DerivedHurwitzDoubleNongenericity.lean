import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedHurwitzGenus49SquareCubeLocking
import Omega.DerivedConsequences.DerivedHurwitzV2WeilNonprimitive

namespace Omega.DerivedConsequences

/-- Paper label: `cor:derived-hurwitz-double-nongenericity`. -/
theorem paper_derived_hurwitz_double_nongenericity :
    derived_hurwitz_v2_weil_nonprimitive_statement ∧
      (derived_hurwitz_genus49_square_cube_locking_factors.map
            derived_hurwitz_genus49_square_cube_locking_factor.multiplicity =
          [1, 2, 3, 3] ∧
        derived_hurwitz_genus49_square_cube_locking_total_dimension = 49) := by
  rcases paper_derived_hurwitz_genus49_square_cube_locking with
    ⟨_, hmultiplicity, _, htotal, _, _, _, _⟩
  exact ⟨paper_derived_hurwitz_v2_weil_nonprimitive, hmultiplicity, htotal⟩

end Omega.DerivedConsequences
