import Mathlib.Tactic
import Omega.Folding.FiberTruncatedMomentCompleteInversion

namespace Omega.OperatorAlgebra

open Omega.Folding

/-- The count of the spectral value `2` recovered from the first three collision moments. -/
def foldWatataniRecoveredCount2 (m : Nat) : ℤ :=
  (12 * foldTruncatedMoment m 0 - 7 * foldTruncatedMoment m 1 + foldTruncatedMoment m 2) / 2

/-- The count of the spectral value `3` recovered from the first three collision moments. -/
def foldWatataniRecoveredCount3 (m : Nat) : ℤ :=
  -8 * foldTruncatedMoment m 0 + 6 * foldTruncatedMoment m 1 - foldTruncatedMoment m 2

/-- The count of the spectral value `4` recovered from the first three collision moments. -/
def foldWatataniRecoveredCount4 (m : Nat) : ℤ :=
  (6 * foldTruncatedMoment m 0 - 5 * foldTruncatedMoment m 1 + foldTruncatedMoment m 2) / 2

/-- The characteristic polynomial attached to the concrete Watatani-index spectrum
`{2, 3, 4}` with the audited multiplicities. -/
def foldWatataniSpectrumCharacteristicPolynomial (m : Nat) (z : ℤ) : ℤ :=
  (1 - 2 * z) ^ Int.toNat (foldTruncatedHistogram2 m) *
    (1 - 3 * z) ^ Int.toNat (foldTruncatedHistogram3 m) *
    (1 - 4 * z) ^ Int.toNat (foldTruncatedHistogram4 m)

/-- The same characteristic polynomial, but built from the counts reconstructed from the first
three collision moments. -/
def foldWatataniRecoveredCharacteristicPolynomial (m : Nat) (z : ℤ) : ℤ :=
  (1 - 2 * z) ^ Int.toNat (foldWatataniRecoveredCount2 m) *
    (1 - 3 * z) ^ Int.toNat (foldWatataniRecoveredCount3 m) *
    (1 - 4 * z) ^ Int.toNat (foldWatataniRecoveredCount4 m)

/-- Concrete finite-support identifiability package: the first three collision moments recover the
three multiplicities on the support `{2, 3, 4}`, hence also the characteristic polynomial of the
Watatani-index spectrum. -/
def FoldWatataniIndexSpectrumFromCollisionMomentsStatement (m : Nat) : Prop :=
  foldWatataniRecoveredCount2 m = foldTruncatedHistogram2 m ∧
    foldWatataniRecoveredCount3 m = foldTruncatedHistogram3 m ∧
    foldWatataniRecoveredCount4 m = foldTruncatedHistogram4 m ∧
    ∀ z : ℤ,
      foldWatataniRecoveredCharacteristicPolynomial m z =
        foldWatataniSpectrumCharacteristicPolynomial m z

/-- Paper label: `thm:op-algebra-watatani-index-spectrum-identifiable-from-collision-moments`.
In the concrete `{2, 3, 4}`-supported model, the first three collision moments recover the fiber
counts by the audited Newton/Vandermonde inversion formulas, so the Watatani-index characteristic
polynomial is reconstructed exactly from those moments. -/
theorem paper_op_algebra_watatani_index_spectrum_identifiable_from_collision_moments (m : Nat) :
    FoldWatataniIndexSpectrumFromCollisionMomentsStatement m := by
  rcases paper_fold_fiber_truncated_moment_complete_inversion m with
    ⟨_, _, h2, h3, h4, _, _, _⟩
  refine ⟨h2, h3, h4, ?_⟩
  intro z
  have h2nat : Int.toNat (foldWatataniRecoveredCount2 m) = Int.toNat (foldTruncatedHistogram2 m) :=
    congrArg Int.toNat h2
  have h3nat : Int.toNat (foldWatataniRecoveredCount3 m) = Int.toNat (foldTruncatedHistogram3 m) :=
    congrArg Int.toNat h3
  have h4nat : Int.toNat (foldWatataniRecoveredCount4 m) = Int.toNat (foldTruncatedHistogram4 m) :=
    congrArg Int.toNat h4
  simp [foldWatataniRecoveredCharacteristicPolynomial,
    foldWatataniSpectrumCharacteristicPolynomial, h2nat, h3nat, h4nat]

end Omega.OperatorAlgebra
