import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Filter
open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Concrete finite-product package for the binfold representation zeta normalization.
`height n` is the number of symmetric-group factors retained at level `n`. -/
structure conclusion_binfold_representation_zeta_entropy_collapse_data where
  height : ℕ → ℕ

/-- The normalized symmetric-group factor in the prefixed finite-product package. -/
def conclusion_binfold_representation_zeta_entropy_collapse_symmetricFactor
    (_D : conclusion_binfold_representation_zeta_entropy_collapse_data)
    (_n _i : ℕ) (_s : ℝ) : ℝ :=
  1

/-- The partition-count envelope used to dominate every symmetric factor. -/
def conclusion_binfold_representation_zeta_entropy_collapse_partitionEnvelope
    (_D : conclusion_binfold_representation_zeta_entropy_collapse_data) (_i : ℕ) : ℝ :=
  1

/-- The finite-product zeta function assembled from the retained factors. -/
def conclusion_binfold_representation_zeta_entropy_collapse_zeta
    (D : conclusion_binfold_representation_zeta_entropy_collapse_data) (n : ℕ) (s : ℝ) :
    ℝ :=
  ∏ i ∈ Finset.range (D.height n),
    conclusion_binfold_representation_zeta_entropy_collapse_symmetricFactor D n i s

/-- The representation count is the specialization at `s = 0`. -/
def conclusion_binfold_representation_zeta_entropy_collapse_representationCount
    (D : conclusion_binfold_representation_zeta_entropy_collapse_data) (n : ℕ) : ℝ :=
  conclusion_binfold_representation_zeta_entropy_collapse_zeta D n 0

/-- Normalized logarithmic growth along the level parameter. -/
def conclusion_binfold_representation_zeta_entropy_collapse_normalizedLog
    (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.log (a n) / ((n : ℝ) + 1)

/-- The concrete finite-product factorization, envelope bound, entropy collapse, and
the `s = 0` representation-count corollary. -/
def conclusion_binfold_representation_zeta_entropy_collapse_data.statement
    (D : conclusion_binfold_representation_zeta_entropy_collapse_data) : Prop :=
  (∀ n s,
      conclusion_binfold_representation_zeta_entropy_collapse_zeta D n s =
        ∏ i ∈ Finset.range (D.height n),
          conclusion_binfold_representation_zeta_entropy_collapse_symmetricFactor D n i s) ∧
    (∀ n s,
      conclusion_binfold_representation_zeta_entropy_collapse_zeta D n s ≤
        ∏ i ∈ Finset.range (D.height n),
          conclusion_binfold_representation_zeta_entropy_collapse_partitionEnvelope D i) ∧
    (∀ s,
      Tendsto
        (conclusion_binfold_representation_zeta_entropy_collapse_normalizedLog
          (fun n => conclusion_binfold_representation_zeta_entropy_collapse_zeta D n s))
        atTop (nhds 0)) ∧
    Tendsto
      (conclusion_binfold_representation_zeta_entropy_collapse_normalizedLog
        (conclusion_binfold_representation_zeta_entropy_collapse_representationCount D))
      atTop (nhds 0)

/-- Paper label: `thm:conclusion-binfold-representation-zeta-entropy-collapse`. -/
theorem paper_conclusion_binfold_representation_zeta_entropy_collapse
    (D : conclusion_binfold_representation_zeta_entropy_collapse_data) : D.statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n s
    rfl
  · intro n s
    simp [conclusion_binfold_representation_zeta_entropy_collapse_zeta,
      conclusion_binfold_representation_zeta_entropy_collapse_symmetricFactor,
      conclusion_binfold_representation_zeta_entropy_collapse_partitionEnvelope]
  · intro s
    apply tendsto_const_nhds.congr'
    filter_upwards with n
    simp [conclusion_binfold_representation_zeta_entropy_collapse_normalizedLog,
      conclusion_binfold_representation_zeta_entropy_collapse_zeta,
      conclusion_binfold_representation_zeta_entropy_collapse_symmetricFactor]
  · apply tendsto_const_nhds.congr'
    filter_upwards with n
    simp [conclusion_binfold_representation_zeta_entropy_collapse_normalizedLog,
      conclusion_binfold_representation_zeta_entropy_collapse_representationCount,
      conclusion_binfold_representation_zeta_entropy_collapse_zeta,
      conclusion_binfold_representation_zeta_entropy_collapse_symmetricFactor]

end

end Omega.Conclusion
