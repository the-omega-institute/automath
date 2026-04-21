import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.POM.BbitOracleCapacityClosedForm

namespace Omega.Folding

open scoped BigOperators

/-- Paper label: `cor:fold-oracle-full-invertibility-threshold`. -/
theorem paper_fold_oracle_full_invertibility_threshold
    {A X : Type*} [Fintype A] [Fintype X] [DecidableEq A] [DecidableEq X] (f : A → X) (B : Nat) :
    Omega.POM.bbitOracleCapacity f B = Fintype.card A ↔
      ∀ x : X, Fintype.card {a : A // f a = x} ≤ 2 ^ B := by
  classical
  let d : X → Nat := fun x => Fintype.card {a : A // f a = x}
  have hcap : Omega.POM.bbitOracleCapacity f B = ∑ x : X, Nat.min (d x) (2 ^ B) := by
    simpa [d] using Omega.POM.paper_pom_bbit_oracle_capacity_closed_form f B
  have hsum : ∑ x : X, d x = Fintype.card A := by
    simpa [d] using (Fintype.sum_fiberwise (g := f) (f := fun _ : A => (1 : Nat)))
  constructor
  · intro hEq x
    by_contra hx
    have hlt : 2 ^ B < d x := Nat.lt_of_not_ge hx
    have hterm : Nat.min (d x) (2 ^ B) < d x := by
      simpa [Nat.min_eq_right (Nat.le_of_lt hlt)] using hlt
    have hrest :
        (Finset.univ.erase x).sum (fun y : X => Nat.min (d y) (2 ^ B)) ≤
          (Finset.univ.erase x).sum (fun y : X => d y) := by
      exact Finset.sum_le_sum (fun y _ => Nat.min_le_left _ _)
    have hltSum : ∑ y : X, Nat.min (d y) (2 ^ B) < ∑ y : X, d y := by
      calc
        ∑ y : X, Nat.min (d y) (2 ^ B)
            = Nat.min (d x) (2 ^ B) +
                (Finset.univ.erase x).sum (fun y : X => Nat.min (d y) (2 ^ B)) := by
                symm
                exact Finset.add_sum_erase (Finset.univ : Finset X)
                  (fun y : X => Nat.min (d y) (2 ^ B)) (Finset.mem_univ x)
        _ < d x + (Finset.univ.erase x).sum (fun y : X => d y) := by
              exact Nat.add_lt_add_of_lt_of_le hterm hrest
        _ = ∑ y : X, d y := by
              exact Finset.add_sum_erase (Finset.univ : Finset X) (fun y : X => d y) (Finset.mem_univ x)
    have hEqSum : ∑ y : X, Nat.min (d y) (2 ^ B) = ∑ y : X, d y := by
      calc
        ∑ y : X, Nat.min (d y) (2 ^ B) = Omega.POM.bbitOracleCapacity f B := hcap.symm
        _ = Fintype.card A := hEq
        _ = ∑ y : X, d y := hsum.symm
    exact (Nat.ne_of_lt hltSum) hEqSum
  · intro hall
    calc
      Omega.POM.bbitOracleCapacity f B = ∑ x : X, Nat.min (d x) (2 ^ B) := hcap
      _ = ∑ x : X, d x := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact Nat.min_eq_left (hall x)
      _ = Fintype.card A := hsum

end Omega.Folding
