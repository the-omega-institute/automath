import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Finite fiber data for the coarse-grained quantum channel. The operator is represented by its
fiber coefficients in the orthogonal projector basis. -/
structure FoldQuantumChannelProjection01RigidityData where
  X : Type
  instDecEqX : DecidableEq X
  instFintypeX : Fintype X
  coeff : X → ℚ

attribute [instance] FoldQuantumChannelProjection01RigidityData.instDecEqX
attribute [instance] FoldQuantumChannelProjection01RigidityData.instFintypeX

namespace FoldQuantumChannelProjection01RigidityData

/-- The channel image is a projection exactly when every fiber coefficient is idempotent. -/
def imageIsProjection (D : FoldQuantumChannelProjection01RigidityData) : Prop :=
  ∀ x, D.coeff x * D.coeff x = D.coeff x

/-- A projector sum is the indicator of a subset of fibers in the canonical fiber basis. -/
def isFiberProjectorSum (D : FoldQuantumChannelProjection01RigidityData) : Prop :=
  ∃ S : Finset D.X, ∀ x, D.coeff x = if x ∈ S then 1 else 0

/-- The commutative fiber-center consists of diagonal `0/1` coefficient functions. -/
def liesInCentralAlgebra (D : FoldQuantumChannelProjection01RigidityData) : Prop :=
  ∃ z : D.X → ℚ, D.coeff = z ∧ ∀ x, z x = 0 ∨ z x = 1

lemma coeff_zero_or_one (D : FoldQuantumChannelProjection01RigidityData)
    (hproj : D.imageIsProjection) (x : D.X) : D.coeff x = 0 ∨ D.coeff x = 1 := by
  have hx : D.coeff x * (D.coeff x - 1) = 0 := by
    nlinarith [hproj x]
  rcases mul_eq_zero.mp hx with h0 | h1
  · left
    linarith
  · right
    linarith

lemma imageIsProjection_iff_isFiberProjectorSum (D : FoldQuantumChannelProjection01RigidityData) :
    D.imageIsProjection ↔ D.isFiberProjectorSum := by
  constructor
  · intro hproj
    let S : Finset D.X := Finset.univ.filter fun x => D.coeff x = 1
    refine ⟨S, ?_⟩
    intro x
    have hx01 := D.coeff_zero_or_one hproj x
    by_cases hx : x ∈ S
    · have hx1 : D.coeff x = 1 := by
        simpa [S] using hx
      simp [hx, hx1]
    · have hx1 : D.coeff x ≠ 1 := by
        intro h1
        apply hx
        simpa [S, h1]
      rcases hx01 with h0 | h1
      · simp [hx, h0]
      · exact False.elim (hx1 h1)
  · rintro ⟨S, hS⟩ x
    by_cases hx : x ∈ S <;> simp [hS x, hx]

lemma isFiberProjectorSum_iff_liesInCentralAlgebra (D : FoldQuantumChannelProjection01RigidityData) :
    D.isFiberProjectorSum ↔ D.liesInCentralAlgebra := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨fun x => if x ∈ S then 1 else 0, ?_, ?_⟩
    · ext x
      simpa [hS x]
    · intro x
      by_cases hx : x ∈ S <;> simp [hx]
  · rintro ⟨z, hz, hz01⟩
    let S : Finset D.X := Finset.univ.filter fun x => z x = 1
    refine ⟨S, ?_⟩
    intro x
    have hcoeff : D.coeff x = z x := by
      simpa using congrArg (fun f => f x) hz
    have hx01 := hz01 x
    by_cases hx : x ∈ S
    · have hz1 : z x = 1 := by
        simpa [S] using hx
      simp [hx, hcoeff, hz1]
    · have hz1 : z x ≠ 1 := by
        intro h1
        apply hx
        simpa [S, h1]
      rcases hx01 with hz0 | hz1'
      · simp [hx, hcoeff, hz0]
      · exact False.elim (hz1 hz1')

end FoldQuantumChannelProjection01RigidityData

open FoldQuantumChannelProjection01RigidityData

/-- Paper label: `prop:op-algebra-fold-quantum-channel-projection-01-rigidity`.
Projection preservation is equivalent to every fiber coefficient being `0` or `1`, hence to the
operator being a sum of fiber projectors, and these sums are exactly the elements of the
commutative fiber-center. -/
theorem paper_op_algebra_fold_quantum_channel_projection_01_rigidity
    (D : FoldQuantumChannelProjection01RigidityData) :
    (D.imageIsProjection ↔ D.isFiberProjectorSum) ∧
      (D.isFiberProjectorSum ↔ D.liesInCentralAlgebra) := by
  exact ⟨D.imageIsProjection_iff_isFiberProjectorSum, D.isFiberProjectorSum_iff_liesInCentralAlgebra⟩

end Omega.OperatorAlgebra
