import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Filter Topology

namespace Omega.Zeta

/-- Paper label: `cor:abelian-tower-no-go`. -/
theorem paper_abelian_tower_no_go (η : ℕ → ℝ) («λ» : ℝ) (hlam : 1 < «λ»)
    (hηlim : Tendsto η Filter.atTop (nhds 1)) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ m : ℕ, η m ≤ «λ» ^ (-((1 / 2 : ℝ) + ε)) := by
  rintro ⟨ε, hε, hbound⟩
  let c : ℝ := «λ» ^ (-((1 / 2 : ℝ) + ε))
  have hexp_neg : -((1 / 2 : ℝ) + ε) < 0 := by linarith
  have hc_lt_one : c < 1 := by
    dsimp [c]
    exact Real.rpow_lt_one_of_one_lt_of_neg hlam hexp_neg
  have hgt : Set.Ioi c ∈ nhds (1 : ℝ) := Ioi_mem_nhds hc_lt_one
  have hevent : ∀ᶠ m in Filter.atTop, c < η m := by
    simpa [Set.mem_Ioi] using hηlim.eventually hgt
  rcases Filter.eventually_atTop.mp hevent with ⟨M, hM⟩
  have hstrict : c < η M := hM M le_rfl
  have hupper : η M ≤ c := by
    simpa [c] using hbound M
  exact (not_le_of_gt hstrict) hupper

end Omega.Zeta
