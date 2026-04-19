import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace Omega.Folding

open scoped BigOperators

noncomputable section

/-- A unit-circle support point packaged together with its norm certificate. -/
abbrev UnitCirclePoint := {z : ℂ // ‖z‖ = 1}

/-- Concrete chapter-local data for the finite atomic approximation used in the
Lee--Yang halting encoding. The data keeps track of finitely many atomic support
points on the unit circle, their weights, and pairwise disjointness. -/
structure HaltingLeyangEncodingData where
  atomCount : ℕ
  q : Fin atomCount → ℕ
  atomPoint : Fin atomCount → UnitCirclePoint
  atomWeight : Fin atomCount → ℚ
  circleWeight : ℚ
  qthRootWitness : ∀ i, (atomPoint i).1 ^ q i = 1
  supportDisjoint : Pairwise fun i j => atomPoint i ≠ atomPoint j

namespace HaltingLeyangEncodingData

/-- The atomic part of the limiting measure. -/
def primeAtomicPart (D : HaltingLeyangEncodingData) (z : UnitCirclePoint) : ℚ :=
  ∑ i : Fin D.atomCount, if D.atomPoint i = z then D.atomWeight i else 0

/-- The circle part of the limiting measure. -/
def lPart (D : HaltingLeyangEncodingData) (_z : UnitCirclePoint) : ℚ :=
  D.circleWeight

/-- The normalized zero-count measure. In this finite model it is exactly the sum of the
continuous `L_N` contribution and the prime-root atomic part. -/
def zeroCountMeasure (D : HaltingLeyangEncodingData) (z : UnitCirclePoint) : ℚ :=
  D.lPart z + D.primeAtomicPart z

/-- The weak-* limit measure used by the chapter-local package. -/
def limitMeasure (D : HaltingLeyangEncodingData) (z : UnitCirclePoint) : ℚ :=
  D.lPart z + D.primeAtomicPart z

/-- Every recorded support point lies on the unit circle. -/
def supportOnUnitCircle (D : HaltingLeyangEncodingData) : Prop :=
  ∀ i : Fin D.atomCount, ‖(D.atomPoint i).1‖ = 1

/-- The normalized zero-count measures stabilize to the declared limit measure. -/
def hasWeakStarLimit (D : HaltingLeyangEncodingData) : Prop :=
  ∀ z : UnitCirclePoint, D.zeroCountMeasure z = D.limitMeasure z

/-- The limit measure decomposes into the `L_N` part plus the prime-root atoms. -/
def limitFormula (D : HaltingLeyangEncodingData) : Prop :=
  ∀ z : UnitCirclePoint, D.limitMeasure z = D.lPart z + D.primeAtomicPart z

/-- Reading the mass at a prime-root atom recovers its weight because the atomic supports are
pairwise disjoint. -/
def atomicRecovery (D : HaltingLeyangEncodingData) : Prop :=
  ∀ i : Fin D.atomCount, D.primeAtomicPart (D.atomPoint i) = D.atomWeight i

private theorem primeAtomicPart_at_atom (D : HaltingLeyangEncodingData) (i : Fin D.atomCount) :
    D.primeAtomicPart (D.atomPoint i) = D.atomWeight i := by
  classical
  unfold primeAtomicPart
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hneq : D.atomPoint j ≠ D.atomPoint i := D.supportDisjoint hj
    simp [if_neg hneq]
  · intro hi
    simp at hi

end HaltingLeyangEncodingData

open HaltingLeyangEncodingData

/-- Paper label: `thm:fold-computability-halting-leyang-holographic-encoding`. -/
theorem paper_fold_computability_halting_leyang_holographic_encoding
    (D : HaltingLeyangEncodingData) :
    D.supportOnUnitCircle ∧ D.hasWeakStarLimit ∧ D.limitFormula ∧ D.atomicRecovery := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact (D.atomPoint i).property
  · intro z
    rfl
  · intro z
    rfl
  · intro i
    exact HaltingLeyangEncodingData.primeAtomicPart_at_atom D i

end

end Omega.Folding
