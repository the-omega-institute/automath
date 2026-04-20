import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- A finite-fiber tower with one concrete prefix-code choice set on each layer. The layerwise
Shannon bounds are packaged directly on the fiber conditionals. -/
structure LayeredFiniteFiberTower where
  BaseMeasure : Type
  depth : ℕ
  LayerCode : Fin depth → Type
  conditionalEntropyLayer : Fin depth → BaseMeasure → Real
  layerLength : (μ : BaseMeasure) → (j : Fin depth) → LayerCode j → Real
  layerLower :
    ∀ (μ : BaseMeasure) (j : Fin depth) (c : LayerCode j),
      conditionalEntropyLayer j μ / Real.log 2 ≤ layerLength μ j c
  layerUpper :
    ∀ (μ : BaseMeasure) (j : Fin depth),
      ∃ c : LayerCode j, layerLength μ j c ≤ conditionalEntropyLayer j μ / Real.log 2 + 1

/-- A global code chooses one layerwise code in every fiber layer. -/
def LayeredFiniteFiberTower.PrefixCodeSystem (T : LayeredFiniteFiberTower) :=
  ∀ j : Fin T.depth, T.LayerCode j

/-- Average externalization length is the sum of the layerwise expected code lengths. -/
def LayeredFiniteFiberTower.averageLength (T : LayeredFiniteFiberTower) (μ : T.BaseMeasure)
    (c : T.PrefixCodeSystem) : Real :=
  ∑ j : Fin T.depth, T.layerLength μ j (c j)

/-- The total Shannon budget is the sum of the layerwise conditional entropies. -/
def LayeredFiniteFiberTower.conditionalEntropySum (T : LayeredFiniteFiberTower)
    (μ : T.BaseMeasure) : Real :=
  ∑ j : Fin T.depth, T.conditionalEntropyLayer j μ

private lemma conditionalEntropySum_div_log_two (T : LayeredFiniteFiberTower) (μ : T.BaseMeasure) :
    T.conditionalEntropySum μ / Real.log 2 =
      ∑ j : Fin T.depth, T.conditionalEntropyLayer j μ / Real.log 2 := by
  simp [LayeredFiniteFiberTower.conditionalEntropySum, div_eq_mul_inv, Finset.sum_mul]

/-- Summing the Shannon lower bound on each fiber gives the global average-length lower bound,
while choosing Shannon-Fano codes layerwise gives the `+ depth` upper bound.
    thm:xi-layered-externalization-average-shannon-budget -/
theorem paper_xi_layered_externalization_average_shannon_budget
    (T : LayeredFiniteFiberTower) (μ : T.BaseMeasure) :
    (∀ c : T.PrefixCodeSystem,
        T.averageLength μ c >= T.conditionalEntropySum μ / Real.log 2) ∧
      ∃ c : T.PrefixCodeSystem,
        T.averageLength μ c <= T.conditionalEntropySum μ / Real.log 2 + T.depth := by
  classical
  constructor
  · intro c
    have hsum :
        ∑ j : Fin T.depth, T.conditionalEntropyLayer j μ / Real.log 2 ≤
          ∑ j : Fin T.depth, T.layerLength μ j (c j) := by
      exact Finset.sum_le_sum fun j _ => T.layerLower μ j (c j)
    simpa [ge_iff_le, LayeredFiniteFiberTower.averageLength, conditionalEntropySum_div_log_two] using
      hsum
  · choose code hcode using T.layerUpper μ
    refine ⟨fun j => code j, ?_⟩
    have hsum :
        ∑ j : Fin T.depth, T.layerLength μ j (code j) ≤
          ∑ j : Fin T.depth, (T.conditionalEntropyLayer j μ / Real.log 2 + 1) := by
      exact Finset.sum_le_sum fun j _ => hcode j
    calc
      T.averageLength μ (fun j => code j)
          = ∑ j : Fin T.depth, T.layerLength μ j (code j) := rfl
      _ ≤ ∑ j : Fin T.depth, (T.conditionalEntropyLayer j μ / Real.log 2 + 1) := hsum
      _ = (∑ j : Fin T.depth, T.conditionalEntropyLayer j μ / Real.log 2) + T.depth := by
          simp [Finset.sum_add_distrib]
      _ = T.conditionalEntropySum μ / Real.log 2 + T.depth := by
          rw [(conditionalEntropySum_div_log_two T μ).symm]

end Omega.Zeta
