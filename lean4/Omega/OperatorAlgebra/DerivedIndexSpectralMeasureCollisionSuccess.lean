import Mathlib.Tactic
import Omega.Folding.OracleCapacityClosedForm
import Omega.OperatorAlgebra.FoldUnlinkEvaluatesToCollisionMoment

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum
open scoped BigOperators

/-- A concrete two-fiber fold map: the first two atoms map to `false`, the last two to `true`. -/
def derivedIndexFold : Fin 4 → Bool :=
  fun i => i.1 < 2

lemma derivedIndexFold_fiber_card (x : Bool) :
    Fintype.card (foldFiber derivedIndexFold x) = 2 := by
  cases x <;> decide

lemma derivedIndexFold_index_coefficient (x : Bool) :
    foldWatataniIndexCoefficient derivedIndexFold x = 2 := by
  unfold foldWatataniIndexCoefficient
  simpa using derivedIndexFold_fiber_card x

/-- Finite spectral average of the central Watatani index field with a `2^B` cap. -/
def derivedIndexSpectralAverage (B q : ℕ) : ℚ :=
  (∑ x : Bool,
      (Nat.min (foldWatataniIndexCoefficient derivedIndexFold x) (2 ^ B) : ℚ) *
        (foldWatataniIndexCoefficient derivedIndexFold x : ℚ) ^ q) /
    Fintype.card (Fin 4)

/-- The traced collision moment extracted from the Watatani index element. -/
def derivedIndexCollisionMoment (q : ℕ) : ℚ :=
  foldWatataniTracedIndexMoment derivedIndexFold q

/-- The binary-coded oracle success count for the same fold map. -/
def derivedIndexOracleSuccess (B : ℕ) : ℕ :=
  Omega.POM.bbitOracleCapacity derivedIndexFold B

/-- Paper-facing common-spectral-data package: the collision moments are the `B = 1` spectral
averages, while the oracle-success curve is the `q = 0` evaluation of the same capped spectral
data. -/
def DerivedIndexSpectralMeasureCollisionSuccessStatement : Prop :=
  (∀ q : ℕ, derivedIndexCollisionMoment q = derivedIndexSpectralAverage 1 q) ∧
    (∀ B : ℕ, derivedIndexOracleSuccess B = 2 * Nat.min 2 (2 ^ B)) ∧
    ∀ B : ℕ,
      (derivedIndexOracleSuccess B : ℚ) =
        (Fintype.card (Fin 4) : ℚ) * derivedIndexSpectralAverage B 0

/-- Paper label: `thm:derived-index-spectral-measure-collision-success`. In the concrete
two-fiber model, the traced Watatani moments and the oracle-success counts are both evaluations
of the same capped multiplicity field, so they are two tests of one spectral measure. -/
theorem paper_derived_index_spectral_measure_collision_success :
    DerivedIndexSpectralMeasureCollisionSuccessStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    have hmoment :=
      (paper_op_algebra_fold_watatani_index_moments derivedIndexFold 2 q (by norm_num)).2.2
    calc
      derivedIndexCollisionMoment q = 2 * (2 ^ (q + 1)) / 4 := by
        simpa [derivedIndexCollisionMoment, foldWatataniIndexCoefficient,
          derivedIndexFold_fiber_card] using hmoment
      _ = 2 * (2 * 2 ^ q) / 4 := by rw [pow_succ]; ring
      _ = derivedIndexSpectralAverage 1 q := by
        unfold derivedIndexSpectralAverage
        simp [derivedIndexFold_index_coefficient]
  · intro B
    have htrue : Fintype.card { ω : Fin 4 // derivedIndexFold ω = true } = 2 := by
      simpa [FoldJonesBasicConstructionDirectsum.foldFiber] using derivedIndexFold_fiber_card true
    have hfalse : Fintype.card { ω : Fin 4 // derivedIndexFold ω = false } = 2 := by
      simpa [FoldJonesBasicConstructionDirectsum.foldFiber] using derivedIndexFold_fiber_card false
    unfold derivedIndexOracleSuccess
    rw [Omega.Folding.paper_fold_oracle_capacity_closed_form derivedIndexFold B]
    simp [htrue, hfalse, two_mul]
  · intro B
    have hsucc : derivedIndexOracleSuccess B = 2 * Nat.min 2 (2 ^ B) := by
      have htrue : Fintype.card { ω : Fin 4 // derivedIndexFold ω = true } = 2 := by
        simpa [FoldJonesBasicConstructionDirectsum.foldFiber] using derivedIndexFold_fiber_card true
      have hfalse : Fintype.card { ω : Fin 4 // derivedIndexFold ω = false } = 2 := by
        simpa [FoldJonesBasicConstructionDirectsum.foldFiber] using derivedIndexFold_fiber_card false
      unfold derivedIndexOracleSuccess
      rw [Omega.Folding.paper_fold_oracle_capacity_closed_form derivedIndexFold B]
      simp [htrue, hfalse, two_mul]
    rw [hsucc]
    unfold derivedIndexSpectralAverage
    norm_num
    simp [derivedIndexFold_index_coefficient]
    ring

end Omega.OperatorAlgebra
