import Mathlib

namespace Omega.POM

/-- The two binary pairings on two ordered pairs of coarse cells. -/
inductive BinaryExtremalPairing
  | consecutive
  | oppositeEnd
  deriving DecidableEq

/-- Concrete ordered data for the binary coarse-graining pairing problem. The score uses the
concave kernel `t ↦ -t^2` on pairwise sums. -/
structure BinaryPairingExtremalData where
  xLo : ℝ
  xHi : ℝ
  yLo : ℝ
  yHi : ℝ
  hx : xLo ≤ xHi
  hy : yLo ≤ yHi

namespace BinaryPairingExtremalData

/-- Chapter-local pairing type. -/
abbrev Pairing (_D : BinaryPairingExtremalData) := BinaryExtremalPairing

/-- The adjacent/consecutive pairing. -/
def consecutivePairing (_D : BinaryPairingExtremalData) : Pairing _D := .consecutive

/-- The opposite-end pairing. -/
def oppositeEndPairing (_D : BinaryPairingExtremalData) : Pairing _D := .oppositeEnd

/-- Score functional attached to the concave kernel `t ↦ -t^2`. -/
def score (D : BinaryPairingExtremalData) : D.Pairing → ℝ
  | .consecutive => -((D.xLo + D.yLo) ^ 2 + (D.xHi + D.yHi) ^ 2)
  | .oppositeEnd => -((D.xLo + D.yHi) ^ 2 + (D.xHi + D.yLo) ^ 2)

lemma score_consecutive_le_oppositeEnd (D : BinaryPairingExtremalData) :
    D.score D.consecutivePairing ≤ D.score D.oppositeEndPairing := by
  have hx' : 0 ≤ D.xHi - D.xLo := sub_nonneg.mpr D.hx
  have hy' : 0 ≤ D.yHi - D.yLo := sub_nonneg.mpr D.hy
  have hnonneg : 0 ≤ 2 * (D.xHi - D.xLo) * (D.yHi - D.yLo) := by positivity
  have hdiff :
      D.score D.oppositeEndPairing - D.score D.consecutivePairing =
        2 * (D.xHi - D.xLo) * (D.yHi - D.yLo) := by
    simp [score, consecutivePairing, oppositeEndPairing]
    ring
  nlinarith

end BinaryPairingExtremalData

open BinaryPairingExtremalData

/-- Paper label: `prop:pom-binary-coarsegraining-concave-pairing-extremes`. For the concave kernel
`t ↦ -t^2`, the consecutive pairing minimizes the two-block score while the opposite-end pairing
maximizes it. -/
theorem paper_pom_binary_coarsegraining_concave_pairing_extremes
    (D : BinaryPairingExtremalData) (P : D.Pairing) :
    D.score D.consecutivePairing <= D.score P ∧ D.score P <= D.score D.oppositeEndPairing := by
  have hExt : D.score D.consecutivePairing ≤ D.score D.oppositeEndPairing :=
    D.score_consecutive_le_oppositeEnd
  cases P
  · exact ⟨le_rfl, hExt⟩
  · exact ⟨hExt, le_rfl⟩

end Omega.POM
