import Mathlib.Tactic
import Omega.POM.OracleCapacityStieltjesInversionMellin
import Omega.POM.SideinfoExactEntropy

namespace Omega.Folding

/-- The finite-threshold capacity profile determines both the tail counts and the exact
multiplicity histogram by discrete differentiation. -/
theorem paper_fold_oracle_capacity_slope_jumps_determine_histogram
    {A X : Type*} [Fintype A] [Fintype X] [DecidableEq A] [DecidableEq X] (f : A → X) :
    let d : X → Nat := Omega.POM.oracleFiberMultiplicity f
    let C : Nat → Nat := fun T => ∑ x : X, Nat.min (d x) T
    (∀ t : Nat, 1 ≤ t → (∑ x : X, if t ≤ d x then 1 else 0) = C t - C (t - 1)) ∧
      (∀ t : Nat,
        (∑ x : X, if d x = t then 1 else 0) =
          (∑ x : X, if t ≤ d x then 1 else 0) -
            (∑ x : X, if t + 1 ≤ d x then 1 else 0)) := by
  simpa [Omega.POM.oracleFiberMultiplicity] using
    (Omega.POM.paper_pom_tary_oracle_capacity_and_inversion (f := f))

end Omega.Folding
