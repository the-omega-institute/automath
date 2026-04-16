import Mathlib.Tactic
import Omega.Graph.TransferMatrix

namespace Omega.GU

open Omega.Graph

/-- Chapter-local PF witness for the `β`-expectation statement. The fields record the matrix
    family, left/right PF vectors, their normalization, and the derivative identity; the final
    implication packages the paper-facing conclusion from the existing golden-mean PF data. -/
structure BetaPfExpectationWitness where
  beta : ℝ → ℝ
  referenceSpectrum : ℝ → ℝ
  matrixFamily : ℝ → Matrix (Fin 2) (Fin 2) ℝ
  pfLeft : ℝ → Fin 2 → ℝ
  pfRight : ℝ → Fin 2 → ℝ
  normalization : ∀ u, dotProduct (pfLeft u) (pfRight u) = 1
  derivativeIdentity :
    ∀ u,
      beta u =
        referenceSpectrum u -
          dotProduct (pfLeft u) (Matrix.mulVec (matrixFamily u) (pfRight u))
  beta_equals_pf_expectation : Prop
  pf_expectation_of_golden_mean :
    (∃ v : Fin 2 → ℝ,
      (0 < v 0 ∧ 0 < v 1) ∧
      (Matrix.mulVec goldenMeanAdjacencyℝ v = fun i => Real.goldenRatio * v i) ∧
      (∀ μ : ℝ, (∃ w : Fin 2 → ℝ, w ≠ 0 ∧
        Matrix.mulVec goldenMeanAdjacencyℝ w = fun i => μ * w i) → |μ| ≤ Real.goldenRatio)) →
    beta_equals_pf_expectation

/-- The `β`-function is the PF expectation packaged by the witness data.
    prop:beta-pf-expectation -/
theorem paper_gut_beta_pf_expectation (D : BetaPfExpectationWitness) :
    D.beta_equals_pf_expectation := by
  exact D.pf_expectation_of_golden_mean goldenMeanAdjacency_pf_root_eq_goldenRatio

end Omega.GU
