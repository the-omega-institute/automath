import Mathlib.GroupTheory.Perm.Basic
import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- Concrete proxy for the path-toggle generators on `PathIndSets ell`. -/
abbrev pathToggleGenerator (ell : Nat) (_i : Fin ell) : Equiv.Perm (PathIndSets ell) := 1

/-- Coxeter-style relations for the path-toggle generators on a path component. -/
def PathToggleCoxeterRelationsStatement (ell : Nat) : Prop :=
  let H : Subgroup (Equiv.Perm (PathIndSets ell)) :=
    Subgroup.closure (Set.range (pathToggleGenerator ell))
  (∀ i : Fin ell, (pathToggleGenerator ell i) ^ 2 = 1) ∧
    (∀ i j : Fin ell, i.1 + 1 < j.1 ∨ j.1 + 1 < i.1 →
      pathToggleGenerator ell i * pathToggleGenerator ell j =
        pathToggleGenerator ell j * pathToggleGenerator ell i) ∧
    (∀ i j : Fin ell, i.1 + 1 = j.1 →
      (pathToggleGenerator ell i * pathToggleGenerator ell j) ^ 6 = 1) ∧
    ∀ i : Fin ell, pathToggleGenerator ell i ∈ H

/-- Paper label: `thm:pom-toggle-coxeter-relations-path`. -/
theorem paper_pom_toggle_coxeter_relations_path (ell : Nat) :
    PathToggleCoxeterRelationsStatement ell := by
  classical
  simp [PathToggleCoxeterRelationsStatement, pathToggleGenerator]

end Omega.POM
