import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Conclusion.RealInput40RootUnityGhostCompletePrimitiveDegenerate

namespace Omega.Conclusion

/-- The root-unity ghost layer is exactly the divisibility comb `2m ∣ n`. -/
def conclusion_realinput40_root_unity_ghost_primitive_rank_split_ghost_divisor_comb : Prop :=
  ∀ m n : ℕ,
    2 ≤ m →
      rootUnityGhostAverage m n = if 2 * m ∣ n then (2 : Complex) else 0

/-- The primitive layer is supported only at the length-`2` atom. -/
def conclusion_realinput40_root_unity_ghost_primitive_rank_split_primitive_rank_one : Prop :=
  ∀ u : Complex, ∀ n : ℕ, atomPrimitiveCoeff n u = if n = 2 then u else 0

/-- Paper label: `cor:conclusion-realinput40-root-unity-ghost-primitive-rank-split`.

The existing root-unity ghost/primitive theorem supplies both sides of the rank split: the ghost
average is the exact divisor comb, while primitive sampling sees only the single length-`2`
coordinate. -/
theorem paper_conclusion_realinput40_root_unity_ghost_primitive_rank_split :
    conclusion_realinput40_root_unity_ghost_primitive_rank_split_ghost_divisor_comb ∧
      conclusion_realinput40_root_unity_ghost_primitive_rank_split_primitive_rank_one := by
  refine ⟨?_, ?_⟩
  · intro m n hm
    simpa using
      (paper_conclusion_realinput40_root_unity_ghost_complete_primitive_degenerate
        (1 : Complex) m n hm).2.2
  · intro u n
    simpa using
      (paper_conclusion_realinput40_root_unity_ghost_complete_primitive_degenerate
        u 2 n (by norm_num)).2.1

end Omega.Conclusion
