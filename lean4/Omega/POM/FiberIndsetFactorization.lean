import Mathlib.Data.Fintype.BigOperators
import Omega.POM.FiberBirkhoffFenceIdealLattice

open scoped BigOperators

namespace Omega.POM

private theorem pathIndSet_product_card (lengths : List ℕ) :
    Fintype.card (((i : Fin lengths.length) → Omega.PathIndSets (lengths.get i))) =
      (lengths.map fun ell => Nat.fib (ell + 2)).prod := by
  calc
    Fintype.card (((i : Fin lengths.length) → Omega.PathIndSets (lengths.get i))) =
        ∏ i : Fin lengths.length, Nat.fib (lengths.get i + 2) := by
          simp [Fintype.card_pi, Omega.card_pathIndSets]
    _ = (lengths.map fun ell => Nat.fib (ell + 2)).prod := by
      induction lengths with
      | nil =>
          simp
      | cons a t ih =>
          calc
            (∏ i : Fin (List.length (a :: t)), Nat.fib ((a :: t).get i + 2)) =
                Nat.fib (a + 2) * ∏ i : Fin t.length, Nat.fib (t.get i + 2) := by
                  simpa using
                    (Fin.prod_univ_succ
                      (f := fun i : Fin (t.length + 1) => Nat.fib ((a :: t).get i + 2)))
            _ = Nat.fib (a + 2) * (List.map (fun ell => Nat.fib (ell + 2)) t).prod := by
                  rw [ih]
            _ = ((a :: t).map fun ell => Nat.fib (ell + 2)).prod := by
                  simp

/-- Paper label: `thm:pom-fiber-indset-factorization`.
Componentwise fiber factors are canonically equivalent to path-independent sets, and the total
fiber cardinality factors as the product of the Fibonacci path counts `F_{ℓ_i+2}`. -/
theorem paper_pom_fiber_indset_factorization (lengths : List ℕ) :
    Nonempty (((i : Fin lengths.length) → Omega.X (lengths.get i)) ≃
      ((i : Fin lengths.length) → Omega.PathIndSets (lengths.get i))) ∧
      Fintype.card (((i : Fin lengths.length) → Omega.PathIndSets (lengths.get i))) =
        (lengths.map fun ell => Nat.fib (ell + 2)).prod ∧
      Fintype.card (((i : Fin lengths.length) → Omega.X (lengths.get i))) =
        (lengths.map fun ell => Nat.fib (ell + 2)).prod := by
  let e : ((i : Fin lengths.length) → Omega.X (lengths.get i)) ≃
      ((i : Fin lengths.length) → Omega.PathIndSets (lengths.get i)) :=
    { toFun := fun x i => Omega.xEquivPathIndSet (lengths.get i) (x i)
      invFun := fun y i => (Omega.xEquivPathIndSet (lengths.get i)).symm (y i)
      left_inv := by
        intro x
        funext i
        exact (Omega.xEquivPathIndSet (lengths.get i)).symm_apply_apply (x i)
      right_inv := by
        intro y
        funext i
        exact (Omega.xEquivPathIndSet (lengths.get i)).apply_symm_apply (y i) }
  have hPath := pathIndSet_product_card lengths
  refine ⟨⟨e⟩, hPath, ?_⟩
  simpa using (Fintype.card_congr e).trans hPath

end Omega.POM
