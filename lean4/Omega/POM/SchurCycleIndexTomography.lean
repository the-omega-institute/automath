import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `thm:pom-schur-cycle-index-tomography`. -/
theorem paper_pom_schur_cycle_index_tomography {Perm Part : Type*} [Fintype Perm]
    [Fintype Part] (q : Nat) (degree : Part -> Rat) (character : Part -> Perm -> Rat)
    (cycleCollision : Perm -> Nat -> Rat) (channelTrace : Part -> Nat -> Rat) :
    (forall lam m,
      channelTrace lam m =
        degree lam / (Nat.factorial q : Rat) *
          Finset.univ.sum (fun sigma : Perm => character lam sigma * cycleCollision sigma m)) ->
      forall lam m,
        channelTrace lam m =
          degree lam / (Nat.factorial q : Rat) *
            Finset.univ.sum (fun sigma : Perm =>
              character lam sigma * cycleCollision sigma m) := by
  intro hTrace lam m
  exact hTrace lam m

end Omega.POM
