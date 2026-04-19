import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.CapacityFiniteCompleteness
import Omega.POM.BbitOracleCapacityClosedForm

namespace Omega.POM

open scoped BigOperators

/-- Fiber multiplicity function attached to the finite map `f`. -/
def oracleFiberMultiplicity {A X : Type*} [Fintype A] [Fintype X] [DecidableEq A] [DecidableEq X]
    (f : A → X) : X → ℕ :=
  fun x => Fintype.card {a : A // f a = x}

/-- Paper-facing finite-support package for oracle-capacity Stieltjes inversion and Mellin
reconstruction. It records the agreement between the continuous capacity curve and the `B`-bit
oracle capacity, together with the histogram/tail/capacity/moment equivalence already formalized
for finite multiplicity data. -/
def oracle_capacity_stieltjes_mellin_package {A X : Type*} [Fintype A] [Fintype X]
    [DecidableEq A] [DecidableEq X] (f : A → X) : Prop :=
  let d : X → ℕ := oracleFiberMultiplicity f
  let h : ℕ → ℕ := fun k => Fintype.card {x : X // d x = k}
  let N : ℕ → ℕ := fun t => Fintype.card {x : X // t ≤ d x}
  let C : ℕ → ℕ := fun t => Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d t
  let S : ℕ → ℕ := fun q => ∑ x : X, d x ^ q
  (∀ B : ℕ, C (2 ^ B) = bbitOracleCapacity f B) ∧
    Omega.Conclusion.FiniteMultiplicityDataEquivalent (X := X) h N C S

/-- Paper label: `thm:pom-oracle-capacity-stieltjes-inversion-mellin`. -/
theorem paper_pom_oracle_capacity_stieltjes_inversion_mellin {A X : Type*} [Fintype A]
    [Fintype X] [DecidableEq A] [DecidableEq X] (f : A → X) :
    oracle_capacity_stieltjes_mellin_package f := by
  dsimp [oracle_capacity_stieltjes_mellin_package, oracleFiberMultiplicity]
  refine ⟨?_, ?_⟩
  · intro B
    simp [oracleFiberMultiplicity, Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve,
      bbitOracleCapacity, taryOracleCapacity]
  · exact Omega.Conclusion.paper_conclusion_capacity_finite_completeness
      (X := X) (d := fun x => Fintype.card {a : A // f a = x})

end Omega.POM
