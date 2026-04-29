import Mathlib.Tactic
import Omega.Folding.BinFold

open scoped BigOperators

namespace Omega.Zeta

/-- The prefixed min-faithful proxy: sum of bin-fold fiber multiplicities over `X m`. -/
noncomputable def xi_time_part60aca_minimal_faithful_dimension_microstate_count_minFaithfulDim
    (m : ℕ) : ℕ :=
  ∑ x : Omega.X m, Omega.cBinFiberMult m x

private def xi_time_part60aca_minimal_faithful_dimension_microstate_count_fiberSet
    (m : ℕ) (x : Omega.X m) : Finset ℕ :=
  (Finset.range (2 ^ m)).filter (fun N => Omega.cBinFold m N = x)

private theorem xi_time_part60aca_minimal_faithful_dimension_microstate_count_sum_eq_pow
    (m : ℕ) : ∑ x : Omega.X m, Omega.cBinFiberMult m x = 2 ^ m := by
  classical
  let fiberSet := xi_time_part60aca_minimal_faithful_dimension_microstate_count_fiberSet m
  have hDisjoint : (↑(Finset.univ : Finset (Omega.X m)) : Set (Omega.X m)).PairwiseDisjoint
      fiberSet := by
    intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro N hx hy
    exact hxy ((Finset.mem_filter.1 hx).2.symm.trans (Finset.mem_filter.1 hy).2)
  have hUnion :
      Finset.range (2 ^ m) = (Finset.univ : Finset (Omega.X m)).biUnion fiberSet := by
    ext N
    simp only [Finset.mem_range, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro hN
      refine ⟨Omega.cBinFold m N, ?_⟩
      simp [fiberSet, xi_time_part60aca_minimal_faithful_dimension_microstate_count_fiberSet,
        hN]
    · intro hN
      rcases hN with ⟨x, hx⟩
      exact Finset.mem_range.1 ((Finset.mem_filter.1 hx).1)
  calc
    ∑ x : Omega.X m, Omega.cBinFiberMult m x
        = ∑ x : Omega.X m, (fiberSet x).card := by
            simp [fiberSet, xi_time_part60aca_minimal_faithful_dimension_microstate_count_fiberSet,
              Omega.cBinFiberMult]
    _ = ((Finset.univ : Finset (Omega.X m)).biUnion fiberSet).card :=
      (Finset.card_biUnion hDisjoint).symm
    _ = (Finset.range (2 ^ m)).card := by rw [hUnion]
    _ = 2 ^ m := Finset.card_range (2 ^ m)

/-- Paper label:
`thm:xi-time-part60aca-minimal-faithful-dimension-microstate-count`. -/
theorem paper_xi_time_part60aca_minimal_faithful_dimension_microstate_count (m : ℕ) :
    xi_time_part60aca_minimal_faithful_dimension_microstate_count_minFaithfulDim m =
      2 ^ m := by
  simpa [xi_time_part60aca_minimal_faithful_dimension_microstate_count_minFaithfulDim]
    using xi_time_part60aca_minimal_faithful_dimension_microstate_count_sum_eq_pow m

end Omega.Zeta
