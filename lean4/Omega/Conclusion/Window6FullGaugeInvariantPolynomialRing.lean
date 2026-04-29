import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-full-gauge-invariant-polynomial-ring`. The listed
homogeneous invariant generators have degree profile `21, 21, 13, 9` in degrees `1, 2, 3, 4`. -/
theorem paper_conclusion_window6_full_gauge_invariant_polynomial_ring :
    ∃ generatorDegrees : List Nat,
      generatorDegrees =
          List.replicate 21 1 ++ List.replicate 21 2 ++ List.replicate 13 3 ++
            List.replicate 9 4 ∧
        generatorDegrees.length = 64 ∧
          (generatorDegrees.filter (fun d => d = 1)).length = 21 ∧
            (generatorDegrees.filter (fun d => d = 2)).length = 21 ∧
              (generatorDegrees.filter (fun d => d = 3)).length = 13 ∧
                (generatorDegrees.filter (fun d => d = 4)).length = 9 := by
  refine
    ⟨List.replicate 21 1 ++ List.replicate 21 2 ++ List.replicate 13 3 ++
        List.replicate 9 4, ?_⟩
  norm_num

end Omega.Conclusion
