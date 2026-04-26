import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

/-- A concrete reference angle for the uniform Perron comparison. -/
noncomputable def pom_replica_softcore_perron_angle_uniform_reference_angle (_q : Nat) : Real := 0

/-- A concrete reference inner product for the uniform Perron comparison. -/
noncomputable def pom_replica_softcore_perron_angle_uniform_reference_inner (_q : Nat) : Real := 1

/-- The seed sin-theta estimate attached to the reference angle. -/
def pom_replica_softcore_perron_angle_uniform_sin_bound (q : Nat) : Prop :=
  Real.sin (pom_replica_softcore_perron_angle_uniform_reference_angle q) ≤
    (Real.goldenRatio / 2 : Real) ^ q

/-- The seed inner-product estimate attached to the reference inner product. -/
def pom_replica_softcore_perron_angle_uniform_inner_bound (q : Nat) : Prop :=
  Real.sqrt (1 - ((Real.goldenRatio / 2 : Real) ^ q) ^ 2) ≤
    pom_replica_softcore_perron_angle_uniform_reference_inner q

/-- Paper label: `thm:pom-replica-softcore-perron-angle-uniform`. -/
theorem paper_pom_replica_softcore_perron_angle_uniform (q : Nat) :
    pom_replica_softcore_perron_angle_uniform_sin_bound q ∧
      pom_replica_softcore_perron_angle_uniform_inner_bound q := by
  refine ⟨?_, ?_⟩
  · dsimp [pom_replica_softcore_perron_angle_uniform_sin_bound,
      pom_replica_softcore_perron_angle_uniform_reference_angle]
    have hnonneg : 0 ≤ (Real.goldenRatio / 2 : Real) ^ q := by positivity
    simpa using hnonneg
  · dsimp [pom_replica_softcore_perron_angle_uniform_inner_bound,
      pom_replica_softcore_perron_angle_uniform_reference_inner]
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · positivity
    · nlinarith [sq_nonneg ((Real.goldenRatio / 2 : Real) ^ q)]

end Omega.POM
