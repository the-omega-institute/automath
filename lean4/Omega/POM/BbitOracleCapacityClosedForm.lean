import Mathlib.Data.Fintype.Card
import Omega.POM.SideinfoExactEntropy

namespace Omega.POM

/-- The `T`-ary oracle capacity written as a reusable global definition. -/
def taryOracleCapacity {A X : Type*} [Fintype A] [Fintype X] [DecidableEq A] [DecidableEq X]
    (f : A → X) (T : Nat) : Nat :=
  ∑ x : X, Nat.min (Fintype.card {a : A // f a = x}) T

/-- The binary-coded specialization of the finite-fiber oracle capacity. -/
def bbitOracleCapacity {A X : Type*} [Fintype A] [Fintype X] [DecidableEq A] [DecidableEq X]
    (f : A → X) (B : Nat) : Nat :=
  taryOracleCapacity f (2 ^ B)

/-- Paper-facing closed form for the `B`-bit oracle inversion capacity.
    cor:pom-bbit-oracle-capacity-closed-form -/
theorem paper_pom_bbit_oracle_capacity_closed_form
    {A X : Type*} [Fintype A] [Fintype X] [DecidableEq A] [DecidableEq X] (f : A → X) (B : Nat) :
    bbitOracleCapacity f B = ∑ x : X, Nat.min (Fintype.card {a : A // f a = x}) (2 ^ B) := by
  simp [bbitOracleCapacity, taryOracleCapacity]

end Omega.POM
