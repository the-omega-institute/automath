import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.POM.BbitOracleCapacityClosedForm
import Omega.POM.OracleCapacityStieltjesInversionMellin

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `prop:fold-oracle-capacity-bimeasure-identity`. -/
theorem paper_fold_oracle_capacity_bimeasure_identity {A X : Type*} [Fintype A] [Fintype X]
    [DecidableEq A] [DecidableEq X] (f : A → X) (B : ℕ) :
    Omega.POM.bbitOracleCapacity f B =
      (∑ x : X,
        if Omega.POM.oracleFiberMultiplicity f x ≤ 2 ^ B then
          Omega.POM.oracleFiberMultiplicity f x
        else 0) +
        (2 ^ B) * Fintype.card {x : X // 2 ^ B < Omega.POM.oracleFiberMultiplicity f x} := by
  let d : X → ℕ := Omega.POM.oracleFiberMultiplicity f
  let small : X → ℕ := fun x => if d x ≤ 2 ^ B then d x else 0
  let large : X → ℕ := fun x => if 2 ^ B < d x then 2 ^ B else 0
  let both : X → ℕ := fun x => small x + large x
  rw [Omega.POM.paper_pom_bbit_oracle_capacity_closed_form]
  change (∑ x : X, Nat.min (d x) (2 ^ B)) =
    (∑ x : X, small x) + (2 ^ B) * Fintype.card {x : X // 2 ^ B < d x}
  have hsplit :
      (∑ x : X, Nat.min (d x) (2 ^ B)) = ∑ x : X, both x := by
    refine Finset.sum_congr rfl ?_
    intro x _
    dsimp [both]
    by_cases hx : d x ≤ 2 ^ B
    · simp [small, large, hx, not_lt_of_ge hx]
    · have hx' : 2 ^ B < d x := Nat.lt_of_not_ge hx
      simp [small, large, hx, hx', Nat.min_eq_right (Nat.le_of_lt hx')]
  rw [hsplit, Finset.sum_add_distrib]
  have hcount :
      (∑ x : X, large x) = Fintype.card {x : X // 2 ^ B < d x} * (2 ^ B) := by
    classical
    unfold large
    rw [← Finset.sum_filter (s := (Finset.univ : Finset X))
      (p := fun x : X => 2 ^ B < d x) (f := fun _ : X => 2 ^ B)]
    simp [Fintype.card_subtype]
  rw [hcount, Nat.mul_comm]

end Omega.POM
