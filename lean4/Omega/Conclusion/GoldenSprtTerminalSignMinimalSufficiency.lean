import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

/-- A stopped golden SPRT path has likelihood-ratio exponent equal to its terminal sign bit.
    thm:conclusion-golden-sprt-terminal-sign-minimal-sufficiency -/
theorem paper_conclusion_golden_sprt_terminal_sign_minimal_sufficiency (T : Nat) (ys : List Int)
    (hstep : forall y, y ∈ ys -> y = 1 \/ y = -1)
    (hstop : ys.sum = (T : Int) \/ ys.sum = -((T : Int))) :
    let ST : Int := if ys.sum = (T : Int) then 1 else -1
    Real.goldenRatio ^ ys.sum = Real.goldenRatio ^ ((T : Int) * ST) := by
  dsimp
  have _ := hstep
  by_cases hsum : ys.sum = (T : Int)
  · simp [hsum]
  · have hneg : ys.sum = -((T : Int)) := by
      rcases hstop with hpos | hneg
      · exact (hsum hpos).elim
      · exact hneg
    have hneq : -((T : Int)) ≠ (T : Int) := by simpa [hneg] using hsum
    have hm : (T : Int) * (-1 : Int) = -((T : Int)) := by ring
    rw [hneg, if_neg hneq, hm]

end Omega.Conclusion
