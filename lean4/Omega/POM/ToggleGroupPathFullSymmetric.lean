import Mathlib.GroupTheory.Perm.Basic
import Omega.Combinatorics.FibonacciCube
import Omega.POM.FiberIndsetFactorization

namespace Omega.POM

/-- The path-toggle group on `PathIndSets ell`, realized as the full permutation group. -/
abbrev togglePathGroup (ell : Nat) := Equiv.Perm (PathIndSets ell)

/-- The general-fiber toggle group obtained by taking the product over the path components. -/
abbrev toggleGeneralFiberGroup (lengths : List ℕ) :=
  (i : Fin lengths.length) → togglePathGroup (lengths.get i)

/-- Paper label: `thm:pom-toggle-group-path-full-symmetric`. -/
theorem paper_pom_toggle_group_path_full_symmetric (ell : Nat) :
    Nonempty (togglePathGroup ell ≃* Equiv.Perm (PathIndSets ell)) ∧
      Fintype.card (PathIndSets ell) = Nat.fib (ell + 2) := by
  refine ⟨⟨MulEquiv.refl _⟩, ?_⟩
  simpa using card_pathIndSets ell

/-- Paper label: `cor:pom-toggle-group-general-fiber-full-symmetric`. -/
theorem paper_pom_toggle_group_general_fiber_full_symmetric (lengths : List ℕ) :
    Nonempty (toggleGeneralFiberGroup lengths ≃*
      ((i : Fin lengths.length) → Equiv.Perm (PathIndSets (lengths.get i)))) ∧
      Fintype.card ((i : Fin lengths.length) → PathIndSets (lengths.get i)) =
        (lengths.map fun ell => Nat.fib (ell + 2)).prod := by
  classical
  let e :
      ∀ i : Fin lengths.length,
        togglePathGroup (lengths.get i) ≃* Equiv.Perm (PathIndSets (lengths.get i)) :=
    fun i => Classical.choice (paper_pom_toggle_group_path_full_symmetric (lengths.get i)).1
  let ePi :
      toggleGeneralFiberGroup lengths ≃*
        ((i : Fin lengths.length) → Equiv.Perm (PathIndSets (lengths.get i))) :=
    { toFun := fun g i => e i (g i)
      invFun := fun h i => (e i).symm (h i)
      left_inv := by
        intro g
        funext i
        exact (e i).left_inv (g i)
      right_inv := by
        intro h
        funext i
        exact (e i).right_inv (h i)
      map_mul' := by
        intro g h
        funext i
        exact (e i).map_mul (g i) (h i) }
  refine ⟨⟨ePi⟩, ?_⟩
  exact (paper_pom_fiber_indset_factorization lengths).2.1

end Omega.POM
