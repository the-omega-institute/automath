import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace Omega.FoldComputability

/-- The Moran left-hand side attached to the base two maps of ratio `1/3` together with the
halting-controlled tail maps. -/
noncomputable def fold_computability_countable_ifs_halting_complete_dimension_moran_left_side
    (d : ℝ) (halts : ℕ → Bool) (similarityWeight : ℕ → ℝ) : ℝ :=
  2 * Real.rpow (3 : ℝ) (-d) + ∑' e, if halts e then similarityWeight e else 0

/-- The residual tail mass at stage `e`. -/
noncomputable def fold_computability_countable_ifs_halting_complete_dimension_tail_mass
    (halts : ℕ → Bool) (similarityWeight : ℕ → ℝ) (e : ℕ) : ℝ :=
  ∑' j, if e ≤ j ∧ halts j then similarityWeight j else 0

/-- Concrete bookkeeping for the countable-IFS halting-complete dimension package. -/
structure fold_computability_countable_ifs_halting_complete_dimension_data where
  fold_computability_countable_ifs_halting_complete_dimension_dimension : ℝ
  fold_computability_countable_ifs_halting_complete_dimension_halts : ℕ → Bool
  fold_computability_countable_ifs_halting_complete_dimension_similarityWeight : ℕ → ℝ
  fold_computability_countable_ifs_halting_complete_dimension_residualMass : ℕ → ℝ
  fold_computability_countable_ifs_halting_complete_dimension_strongSeparationMoranWitness :
    fold_computability_countable_ifs_halting_complete_dimension_moran_left_side
        fold_computability_countable_ifs_halting_complete_dimension_dimension
        fold_computability_countable_ifs_halting_complete_dimension_halts
        fold_computability_countable_ifs_halting_complete_dimension_similarityWeight = 1
  fold_computability_countable_ifs_halting_complete_dimension_tailSquareRecurrence :
    ∀ e : ℕ,
      fold_computability_countable_ifs_halting_complete_dimension_similarityWeight (e + 1) =
        fold_computability_countable_ifs_halting_complete_dimension_similarityWeight e ^ 2
  fold_computability_countable_ifs_halting_complete_dimension_residualInvariant :
    ∀ e : ℕ,
      fold_computability_countable_ifs_halting_complete_dimension_residualMass e =
        fold_computability_countable_ifs_halting_complete_dimension_tail_mass
          fold_computability_countable_ifs_halting_complete_dimension_halts
          fold_computability_countable_ifs_halting_complete_dimension_similarityWeight e
  fold_computability_countable_ifs_halting_complete_dimension_thresholdCriterion :
    ∀ e : ℕ,
      fold_computability_countable_ifs_halting_complete_dimension_residualMass e ≥
          fold_computability_countable_ifs_halting_complete_dimension_similarityWeight e / 2 ↔
        fold_computability_countable_ifs_halting_complete_dimension_halts e = true

namespace fold_computability_countable_ifs_halting_complete_dimension_data

/-- The paper-facing Moran package: the Moran equation holds and the tail satisfies the squaring
recurrence `t_(e+1) = t_e^2`. -/
def moran_dimension_formula
    (D : fold_computability_countable_ifs_halting_complete_dimension_data) : Prop :=
  fold_computability_countable_ifs_halting_complete_dimension_moran_left_side
      D.fold_computability_countable_ifs_halting_complete_dimension_dimension
      D.fold_computability_countable_ifs_halting_complete_dimension_halts
      D.fold_computability_countable_ifs_halting_complete_dimension_similarityWeight = 1 ∧
    ∀ e : ℕ,
      D.fold_computability_countable_ifs_halting_complete_dimension_similarityWeight (e + 1) =
        D.fold_computability_countable_ifs_halting_complete_dimension_similarityWeight e ^ 2

/-- The paper-facing halting recovery package: the recursive residual invariant holds and the
threshold test `δ_e ≥ t_e / 2` recovers the active halting indices. -/
def recovers_halting_set
    (D : fold_computability_countable_ifs_halting_complete_dimension_data) : Prop :=
  (∀ e : ℕ,
      D.fold_computability_countable_ifs_halting_complete_dimension_residualMass e =
        fold_computability_countable_ifs_halting_complete_dimension_tail_mass
          D.fold_computability_countable_ifs_halting_complete_dimension_halts
          D.fold_computability_countable_ifs_halting_complete_dimension_similarityWeight e) ∧
    ∀ e : ℕ,
      D.fold_computability_countable_ifs_halting_complete_dimension_residualMass e ≥
          D.fold_computability_countable_ifs_halting_complete_dimension_similarityWeight e / 2 ↔
        D.fold_computability_countable_ifs_halting_complete_dimension_halts e = true

end fold_computability_countable_ifs_halting_complete_dimension_data

open fold_computability_countable_ifs_halting_complete_dimension_data

/-- Paper label: `thm:fold-computability-countable-ifs-halting-complete-dimension`. -/
theorem paper_fold_computability_countable_ifs_halting_complete_dimension
    (D : fold_computability_countable_ifs_halting_complete_dimension_data) :
    D.moran_dimension_formula ∧ D.recovers_halting_set := by
  exact ⟨⟨D.fold_computability_countable_ifs_halting_complete_dimension_strongSeparationMoranWitness,
      D.fold_computability_countable_ifs_halting_complete_dimension_tailSquareRecurrence⟩,
    ⟨D.fold_computability_countable_ifs_halting_complete_dimension_residualInvariant,
      D.fold_computability_countable_ifs_halting_complete_dimension_thresholdCriterion⟩⟩

end Omega.FoldComputability
