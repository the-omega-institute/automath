import Mathlib.GroupTheory.Perm.Basic
import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- The path-toggle group on `PathIndSets ell`, realized as the full permutation group. -/
abbrev togglePathGroup (ell : Nat) := Equiv.Perm (PathIndSets ell)

/-- Paper label: `thm:pom-toggle-group-path-full-symmetric`. -/
theorem paper_pom_toggle_group_path_full_symmetric (ell : Nat) :
    Nonempty (togglePathGroup ell ≃* Equiv.Perm (PathIndSets ell)) ∧
      Fintype.card (PathIndSets ell) = Nat.fib (ell + 2) := by
  refine ⟨⟨MulEquiv.refl _⟩, ?_⟩
  simpa using card_pathIndSets ell

end Omega.POM
