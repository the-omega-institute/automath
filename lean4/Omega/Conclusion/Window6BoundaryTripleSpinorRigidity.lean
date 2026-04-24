import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The three CRT idempotents for the `2 × 3 × 5` boundary algebra model at modulus `30`. -/
def window6BoundaryIdempotentOne : ZMod 30 := 15

/-- The second CRT idempotent for the `2 × 3 × 5` boundary algebra model at modulus `30`. -/
def window6BoundaryIdempotentTwo : ZMod 30 := 10

/-- The third CRT idempotent for the `2 × 3 × 5` boundary algebra model at modulus `30`. -/
def window6BoundaryIdempotentThree : ZMod 30 := 6

/-- Each faithful boundary summand must contain a full `M₂` block, modeled here by the lower bound
`2 ≤ n` on its representation dimension. -/
def containsFaithfulM2Block (n : Nat) : Prop := 2 ≤ n

/-- Equality means that the summand is exactly one standard `2`-dimensional spinor block. -/
def isStandardSpinorBlock (n : Nat) : Prop := n = 2

/-- Concrete boundary representation data for the three central idempotent summands. -/
structure Window6BoundaryTripleSpinorRigidityData where
  leftDim : Nat
  middleDim : Nat
  rightDim : Nat
  leftFaithful : containsFaithfulM2Block leftDim
  middleFaithful : containsFaithfulM2Block middleDim
  rightFaithful : containsFaithfulM2Block rightDim

/-- Total dimension of the faithful graded representation after splitting by the three orthogonal
central idempotents. -/
def boundaryTripleSpinorTotalDim (D : Window6BoundaryTripleSpinorRigidityData) : Nat :=
  D.leftDim + D.middleDim + D.rightDim

/-- Equality case: each of the three orthogonal summands is exactly one standard spinor block. -/
def standardSpinorOnEachSummand (D : Window6BoundaryTripleSpinorRigidityData) : Prop :=
  isStandardSpinorBlock D.leftDim ∧
    isStandardSpinorBlock D.middleDim ∧
    isStandardSpinorBlock D.rightDim

/-- Concrete statement packaging the three boundary idempotents, the faithful `M₂` lower bound on
each orthogonal summand, and the sharp equality case. -/
def Window6BoundaryTripleSpinorRigidityStatement
    (D : Window6BoundaryTripleSpinorRigidityData) : Prop :=
  window6BoundaryIdempotentOne * window6BoundaryIdempotentOne = window6BoundaryIdempotentOne ∧
    window6BoundaryIdempotentTwo * window6BoundaryIdempotentTwo = window6BoundaryIdempotentTwo ∧
    window6BoundaryIdempotentThree * window6BoundaryIdempotentThree =
      window6BoundaryIdempotentThree ∧
    window6BoundaryIdempotentOne * window6BoundaryIdempotentTwo = 0 ∧
    window6BoundaryIdempotentOne * window6BoundaryIdempotentThree = 0 ∧
    window6BoundaryIdempotentTwo * window6BoundaryIdempotentThree = 0 ∧
    window6BoundaryIdempotentOne + window6BoundaryIdempotentTwo +
        window6BoundaryIdempotentThree = 1 ∧
    containsFaithfulM2Block D.leftDim ∧
    containsFaithfulM2Block D.middleDim ∧
    containsFaithfulM2Block D.rightDim ∧
    6 ≤ boundaryTripleSpinorTotalDim D ∧
    (boundaryTripleSpinorTotalDim D = 6 ↔ standardSpinorOnEachSummand D)

lemma boundaryTripleSpinorTotalDim_eq_six_iff_standard
    (D : Window6BoundaryTripleSpinorRigidityData) :
    boundaryTripleSpinorTotalDim D = 6 ↔ standardSpinorOnEachSummand D := by
  constructor
  · intro h
    have hleft := D.leftFaithful
    have hmiddle := D.middleFaithful
    have hright := D.rightFaithful
    unfold containsFaithfulM2Block at hleft hmiddle hright
    refine ⟨?_, ?_, ?_⟩
    · unfold isStandardSpinorBlock
      unfold boundaryTripleSpinorTotalDim at h
      omega
    · unfold isStandardSpinorBlock
      unfold boundaryTripleSpinorTotalDim at h
      omega
    · unfold isStandardSpinorBlock
      unfold boundaryTripleSpinorTotalDim at h
      omega
  · intro h
    rcases h with ⟨hleft, hmiddle, hright⟩
    unfold boundaryTripleSpinorTotalDim
    have hleft' : D.leftDim = 2 := by simpa [isStandardSpinorBlock] using hleft
    have hmiddle' : D.middleDim = 2 := by simpa [isStandardSpinorBlock] using hmiddle
    have hright' : D.rightDim = 2 := by simpa [isStandardSpinorBlock] using hright
    omega

/-- Paper label: `thm:conclusion-window6-boundary-triple-spinor-rigidity`.
Packaging the boundary algebra by its three central CRT idempotents splits a faithful graded
representation into three orthogonal summands; each summand contains a faithful `M₂` block, so
the total dimension is at least `6`, with equality exactly for one standard spinor block on each
summand. -/
theorem paper_conclusion_window6_boundary_triple_spinor_rigidity
    (D : Window6BoundaryTripleSpinorRigidityData) :
    Window6BoundaryTripleSpinorRigidityStatement D := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    D.leftFaithful, D.middleFaithful, D.rightFaithful, ?_, ?_⟩
  · unfold boundaryTripleSpinorTotalDim
    have hleft := D.leftFaithful
    have hmiddle := D.middleFaithful
    have hright := D.rightFaithful
    unfold containsFaithfulM2Block at hleft hmiddle hright
    omega
  · exact boundaryTripleSpinorTotalDim_eq_six_iff_standard D

end Omega.Conclusion
