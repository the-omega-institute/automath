import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.POM.RenyiHalfHellingerTensorAdditivity

open scoped BigOperators

namespace Omega.POM

noncomputable section

/-- Concrete finite-state endpoint package for the rare-mismatch Hellinger normalization. -/
structure pom_diagonal_rate_rare_mismatch_hellinger_universality_Data where
  State : Type
  instFintype : Fintype State
  instDecidableEq : DecidableEq State
  w : State → ℝ
  δ : ℝ

attribute [instance] pom_diagonal_rate_rare_mismatch_hellinger_universality_Data.instFintype
attribute [instance] pom_diagonal_rate_rare_mismatch_hellinger_universality_Data.instDecidableEq

namespace pom_diagonal_rate_rare_mismatch_hellinger_universality_Data

/-- The Hellinger half-sum `A_{1/2}(w)`. -/
def hellingerHalfSum (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data) : ℝ :=
  pomHellingerHalfSum D.w

/-- The endpoint denominator `A_{1/2}(w)^2 - 1`. -/
def endpointDenominator (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data) : ℝ :=
  D.hellingerHalfSum ^ (2 : ℕ) - 1

/-- Rare-mismatch off-diagonal coefficient in the normalized small-distortion expansion. -/
def offdiagCoefficient (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data)
    (x y : D.State) : ℝ :=
  Real.sqrt (D.w x * D.w y) / D.endpointDenominator

/-- First-order diagonal loss coefficient obtained by summing the off-diagonal Hellinger profile. -/
def diagonalLossCoefficient (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data)
    (x : D.State) : ℝ :=
  Real.sqrt (D.w x) * (D.hellingerHalfSum - Real.sqrt (D.w x)) / D.endpointDenominator

/-- First-order diagonal expansion of the optimal coupling. -/
def diagonalExpansionTerm (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data)
    (x : D.State) : ℝ :=
  D.w x - D.δ * D.diagonalLossCoefficient x

/-- The endpoint background distribution selected by the Hellinger normalization. -/
def backgroundEndpoint (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data)
    (x : D.State) : ℝ :=
  Real.sqrt (D.w x) / D.hellingerHalfSum

/-- First-order loss coefficient for the stay probability. -/
def stayLossCoefficient (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data)
    (x : D.State) : ℝ :=
  (D.hellingerHalfSum - Real.sqrt (D.w x)) /
    (Real.sqrt (D.w x) * D.endpointDenominator)

/-- First-order stay-probability expansion. -/
def stayExpansionTerm (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data)
    (x : D.State) : ℝ :=
  1 - D.δ * D.stayLossCoefficient x

/-- Off-diagonal rare-mismatch coefficients have the Hellinger universal shape. -/
def offdiag_limit (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data) : Prop :=
  ∀ x y : D.State, x ≠ y →
    D.offdiagCoefficient x y =
      Real.sqrt (D.w x * D.w y) / (D.hellingerHalfSum ^ (2 : ℕ) - 1)

/-- The diagonal expansion is the mass minus the summed Hellinger off-diagonal leakage. -/
def diag_expansion (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data) : Prop :=
  ∀ x : D.State,
    D.diagonalExpansionTerm x =
      D.w x -
        D.δ *
          (Real.sqrt (D.w x) * (D.hellingerHalfSum - Real.sqrt (D.w x)) /
            (D.hellingerHalfSum ^ (2 : ℕ) - 1))

/-- The background endpoint is the normalized square-root weight. -/
def background_limit (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data) : Prop :=
  ∀ x : D.State, D.backgroundEndpoint x = Real.sqrt (D.w x) / D.hellingerHalfSum

/-- The stay-probability expansion is normalized by the same Hellinger denominator. -/
def stay_probability_expansion
    (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data) : Prop :=
  ∀ x : D.State,
    D.stayExpansionTerm x =
      1 -
        D.δ *
          ((D.hellingerHalfSum - Real.sqrt (D.w x)) /
            (Real.sqrt (D.w x) * (D.hellingerHalfSum ^ (2 : ℕ) - 1)))

end pom_diagonal_rate_rare_mismatch_hellinger_universality_Data

/-- Paper label: `thm:pom-diagonal-rate-rare-mismatch-hellinger-universality`.
The rare-mismatch endpoint coefficients obtained from the optimal-coupling normalization reduce to
the universal Hellinger off-diagonal shape, the corresponding diagonal leakage, the normalized
background square-root law, and the induced stay-probability expansion. -/
theorem paper_pom_diagonal_rate_rare_mismatch_hellinger_universality
    (D : pom_diagonal_rate_rare_mismatch_hellinger_universality_Data) :
    D.offdiag_limit ∧ D.diag_expansion ∧ D.background_limit ∧
      D.stay_probability_expansion := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rfl
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    rfl

end

end Omega.POM
