import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Chapter-local package for the two-state uniform average of `log d_m`. The two terminal states
share a common main term, with state-dependent error terms. -/
structure XiTimePart70aAverageLogdegData where
  m : ℕ
  mainTerm : ℝ
  zeroError : ℝ
  oneError : ℝ

namespace XiTimePart70aAverageLogdegData

/-- Exact Fibonacci terminal-state weights. -/
def terminalWeight (m : ℕ) : Bool → ℝ
  | false => (Nat.fib (m + 1) : ℝ) / Nat.fib (m + 2)
  | true => (Nat.fib m : ℝ) / Nat.fib (m + 2)

/-- The two terminal-state logarithmic degrees. -/
def terminalLogdeg (D : XiTimePart70aAverageLogdegData) : Bool → ℝ
  | false => D.mainTerm + D.zeroError
  | true => D.mainTerm + D.oneError

/-- The exact weighted two-state average. -/
def averageLogdeg (D : XiTimePart70aAverageLogdegData) : ℝ :=
  terminalWeight D.m false * D.terminalLogdeg false +
    terminalWeight D.m true * D.terminalLogdeg true

/-- The weighted error term. -/
def weightedError (D : XiTimePart70aAverageLogdegData) : ℝ :=
  terminalWeight D.m false * D.zeroError + terminalWeight D.m true * D.oneError

/-- The common main term separates from the exact weighted average, leaving only the weighted
error term. -/
def uniformAverageLogdegTwoState (D : XiTimePart70aAverageLogdegData) : Prop :=
  D.averageLogdeg = D.mainTerm + D.weightedError

lemma terminalWeight_sum (m : ℕ) : terminalWeight m false + terminalWeight m true = 1 := by
  have hdenPos : (0 : ℝ) < Nat.fib (m + 2) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hfib :
      (Nat.fib (m + 1) : ℝ) + (Nat.fib m : ℝ) = (Nat.fib (m + 2) : ℝ) := by
    exact_mod_cast (by simpa [Nat.add_comm] using (Nat.fib_add_two (n := m)).symm)
  calc
    terminalWeight m false + terminalWeight m true
        = ((Nat.fib (m + 1) : ℝ) + (Nat.fib m : ℝ)) / Nat.fib (m + 2) := by
            simp [terminalWeight, add_div]
    _ = (Nat.fib (m + 2) : ℝ) / Nat.fib (m + 2) := by rw [hfib]
    _ = 1 := by field_simp [hdenPos.ne']

end XiTimePart70aAverageLogdegData

open XiTimePart70aAverageLogdegData

/-- Paper label: `thm:xi-time-part70a-uniform-average-logdeg-two-state`. -/
theorem paper_xi_time_part70a_uniform_average_logdeg_two_state
    (D : XiTimePart70aAverageLogdegData) : D.uniformAverageLogdegTwoState := by
  calc
    D.averageLogdeg
        = D.mainTerm *
            (terminalWeight D.m false + terminalWeight D.m true) + D.weightedError := by
              unfold XiTimePart70aAverageLogdegData.averageLogdeg
                XiTimePart70aAverageLogdegData.terminalLogdeg
                XiTimePart70aAverageLogdegData.weightedError
              ring
    _ = D.mainTerm + D.weightedError := by rw [terminalWeight_sum]; ring

end
end Omega.Zeta
